import V185TrunkScan23Chunk0945

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5600270 : List Nat := [4, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4]
def baseStart_5600270 : Nat := 118140960795 + 5600270 * 2 ^ 59
def prefixEnd_5600270 : Nat := 4983230072969 + 3 ^ 40 * 5600270 * 2
def baseEnd_5600270 : Nat := 2875630304954909151569833

theorem tailTrace_5600270 : CollatzResearch.WordTrace tailWord_5600270 prefixEnd_5600270 2875630304954909151569833 := by
  unfold tailWord_5600270
  simp only [CollatzResearch.WordTrace]
  refine ⟨25532328427648214351779783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136172418280790476542825509 25532328427648214351779783)
  ·
    refine ⟨38298492641472321527669675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25532328427648214351779783 38298492641472321527669675)
    ·
      refine ⟨57447738962208482291504513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38298492641472321527669675 57447738962208482291504513)
      ·
        refine ⟨43085804221656361718628385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57447738962208482291504513 43085804221656361718628385)
        ·
          refine ⟨32314353166242271288971289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43085804221656361718628385 32314353166242271288971289)
          ·
            refine ⟨24235764874681703466728467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32314353166242271288971289 24235764874681703466728467)
            ·
              refine ⟨36353647312022555200092701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24235764874681703466728467 36353647312022555200092701)
              ·
                refine ⟨13632617742008458200034763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36353647312022555200092701 13632617742008458200034763)
                ·
                  refine ⟨20448926613012687300052145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13632617742008458200034763 20448926613012687300052145)
                  ·
                    refine ⟨15336694959759515475039109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20448926613012687300052145 15336694959759515475039109)
                    ·
                      refine ⟨2875630304954909151569833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15336694959759515475039109 2875630304954909151569833)
                      ·
                        rfl

theorem cell23_5600270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_5600270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600270 prefixEnd_5600270 := by exact prefixLift 5600270
  have htrace : WordTrace (prefixWord ++ tailWord_5600270) baseStart_5600270 baseEnd_5600270 := by
    simpa [prefixWord, tailWord_5600270, baseEnd_5600270] using wordTrace_append hprefix tailTrace_5600270
  have hstable : (prefixWord ++ tailWord_5600270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600270).length < 2 ^ (prefixWord ++ tailWord_5600270).sum := by decide
  have hdescent : baseEnd_5600270 < baseStart_5600270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600280 : List Nat := [2, 1, 2, 3, 2, 3, 3, 7]
def baseStart_5600280 : Nat := 118140960795 + 5600280 * 2 ^ 59
def prefixEnd_5600280 : Nat := 4983230072969 + 3 ^ 40 * 5600280 * 2
def baseEnd_5600280 : Nat := 106505016287461263423881

theorem tailTrace_5600280 : CollatzResearch.WordTrace tailWord_5600280 prefixEnd_5600280 106505016287461263423881 := by
  unfold tailWord_5600280
  simp only [CollatzResearch.WordTrace]
  refine ⟨102129496075574743261051147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136172661434099657681401529 102129496075574743261051147)
  ·
    refine ⟨153194244113362114891576721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102129496075574743261051147 153194244113362114891576721)
    ·
      refine ⟨114895683085021586168682541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153194244113362114891576721 114895683085021586168682541)
      ·
        refine ⟨43085881156883094813255953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114895683085021586168682541 43085881156883094813255953)
        ·
          refine ⟨32314410867662321109941965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43085881156883094813255953 32314410867662321109941965)
          ·
            refine ⟨12117904075373370416228237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32314410867662321109941965 12117904075373370416228237)
            ·
              refine ⟨4544214028265013906085589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12117904075373370416228237 4544214028265013906085589)
              ·
                refine ⟨106505016287461263423881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4544214028265013906085589 106505016287461263423881)
                ·
                  rfl

theorem cell23_5600280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 7].length) (baseStart_5600280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600280 prefixEnd_5600280 := by exact prefixLift 5600280
  have htrace : WordTrace (prefixWord ++ tailWord_5600280) baseStart_5600280 baseEnd_5600280 := by
    simpa [prefixWord, tailWord_5600280, baseEnd_5600280] using wordTrace_append hprefix tailTrace_5600280
  have hstable : (prefixWord ++ tailWord_5600280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600280).length < 2 ^ (prefixWord ++ tailWord_5600280).sum := by decide
  have hdescent : baseEnd_5600280 < baseStart_5600280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600291 : List Nat := [1, 1, 1, 4, 3, 3, 2, 3, 1, 2, 2]
def baseStart_5600291 : Nat := 118140960795 + 5600291 * 2 ^ 59
def prefixEnd_5600291 : Nat := 4983230072969 + 3 ^ 40 * 5600291 * 2
def baseEnd_5600291 : Nat := 2875641088048653569407237

theorem tailTrace_5600291 : CollatzResearch.WordTrace tailWord_5600291 prefixEnd_5600291 2875641088048653569407237 := by
  unfold tailWord_5600291
  simp only [CollatzResearch.WordTrace]
  refine ⟨204259393354109635400752727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136172928902739756933835151 204259393354109635400752727)
  ·
    refine ⟨306389090031164453101129091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204259393354109635400752727 306389090031164453101129091)
    ·
      refine ⟨459583635046746679651693637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306389090031164453101129091 459583635046746679651693637)
      ·
        refine ⟨86171931571265002434692557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 459583635046746679651693637 86171931571265002434692557)
        ·
          refine ⟨32314474339224375913009709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86171931571265002434692557 32314474339224375913009709)
          ·
            refine ⟨12117927877209140967378641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32314474339224375913009709 12117927877209140967378641)
            ·
              refine ⟨9088445907906855725533981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12117927877209140967378641 9088445907906855725533981)
              ·
                refine ⟨3408167215465070897075243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9088445907906855725533981 3408167215465070897075243)
                ·
                  refine ⟨5112250823197606345612865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3408167215465070897075243 5112250823197606345612865)
                  ·
                    refine ⟨3834188117398204759209649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5112250823197606345612865 3834188117398204759209649)
                    ·
                      refine ⟨2875641088048653569407237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3834188117398204759209649 2875641088048653569407237)
                      ·
                        rfl

theorem cell23_5600291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 3, 1, 2, 2].length) (baseStart_5600291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600291 prefixEnd_5600291 := by exact prefixLift 5600291
  have htrace : WordTrace (prefixWord ++ tailWord_5600291) baseStart_5600291 baseEnd_5600291 := by
    simpa [prefixWord, tailWord_5600291, baseEnd_5600291] using wordTrace_append hprefix tailTrace_5600291
  have hstable : (prefixWord ++ tailWord_5600291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600291).length < 2 ^ (prefixWord ++ tailWord_5600291).sum := by decide
  have hdescent : baseEnd_5600291 < baseStart_5600291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600308 : List Nat := [2, 5, 1, 2, 1, 1, 2, 4, 1, 2, 2]
def baseStart_5600308 : Nat := 118140960795 + 5600308 * 2 ^ 59
def prefixEnd_5600308 : Nat := 4983230072969 + 3 ^ 40 * 5600308 * 2
def baseEnd_5600308 : Nat := 2875649817219780002894659

theorem tailTrace_5600308 : CollatzResearch.WordTrace tailWord_5600308 prefixEnd_5600308 2875649817219780002894659 := by
  unfold tailWord_5600308
  simp only [CollatzResearch.WordTrace]
  refine ⟨102130006697524023652060789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136173342263365364869414385 102130006697524023652060789)
  ·
    refine ⟨9574688127892877217380699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102130006697524023652060789 9574688127892877217380699)
    ·
      refine ⟨14362032191839315826071049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9574688127892877217380699 14362032191839315826071049)
      ·
        refine ⟨10771524143879486869553287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14362032191839315826071049 10771524143879486869553287)
        ·
          refine ⟨16157286215819230304329931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10771524143879486869553287 16157286215819230304329931)
          ·
            refine ⟨24235929323728845456494897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16157286215819230304329931 24235929323728845456494897)
            ·
              refine ⟨18176946992796634092371173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24235929323728845456494897 18176946992796634092371173)
              ·
                refine ⟨3408177561149368892319595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18176946992796634092371173 3408177561149368892319595)
                ·
                  refine ⟨5112266341724053338479393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3408177561149368892319595 5112266341724053338479393)
                  ·
                    refine ⟨3834199756293040003859545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5112266341724053338479393 3834199756293040003859545)
                    ·
                      refine ⟨2875649817219780002894659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3834199756293040003859545 2875649817219780002894659)
                      ·
                        rfl

theorem cell23_5600308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_5600308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600308 prefixEnd_5600308 := by exact prefixLift 5600308
  have htrace : WordTrace (prefixWord ++ tailWord_5600308) baseStart_5600308 baseEnd_5600308 := by
    simpa [prefixWord, tailWord_5600308, baseEnd_5600308] using wordTrace_append hprefix tailTrace_5600308
  have hstable : (prefixWord ++ tailWord_5600308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600308).length < 2 ^ (prefixWord ++ tailWord_5600308).sum := by decide
  have hdescent : baseEnd_5600308 < baseStart_5600308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600323 : List Nat := [1, 1, 1, 3, 1, 2, 3, 3, 2, 6]
def baseStart_5600323 : Nat := 118140960795 + 5600323 * 2 ^ 59
def prefixEnd_5600323 : Nat := 4983230072969 + 3 ^ 40 * 5600323 * 2
def baseEnd_5600323 : Nat := 958552506476532481402363

theorem tailTrace_5600323 : CollatzResearch.WordTrace tailWord_5600323 prefixEnd_5600323 958552506476532481402363 := by
  unfold tailWord_5600323
  simp only [CollatzResearch.WordTrace]
  refine ⟨204260560489993704865917623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136173706993329136577278415 204260560489993704865917623)
  ·
    refine ⟨306390840734990557298876435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204260560489993704865917623 306390840734990557298876435)
    ·
      refine ⟨459586261102485835948314653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306390840734990557298876435 459586261102485835948314653)
      ·
        refine ⟨172344847913432188480617995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 459586261102485835948314653 172344847913432188480617995)
        ·
          refine ⟨258517271870148282720926993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172344847913432188480617995 258517271870148282720926993)
          ·
            refine ⟨193887953902611212040695245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258517271870148282720926993 193887953902611212040695245)
            ·
              refine ⟨72707982713479204515260717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193887953902611212040695245 72707982713479204515260717)
              ·
                refine ⟨27265493517554701693222769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72707982713479204515260717 27265493517554701693222769)
                ·
                  refine ⟨20449120138166026269917077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27265493517554701693222769 20449120138166026269917077)
                  ·
                    refine ⟨958552506476532481402363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20449120138166026269917077 958552506476532481402363)
                    ·
                      rfl

theorem cell23_5600323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 6].length) (baseStart_5600323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600323 prefixEnd_5600323 := by exact prefixLift 5600323
  have htrace : WordTrace (prefixWord ++ tailWord_5600323) baseStart_5600323 baseEnd_5600323 := by
    simpa [prefixWord, tailWord_5600323, baseEnd_5600323] using wordTrace_append hprefix tailTrace_5600323
  have hstable : (prefixWord ++ tailWord_5600323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600323).length < 2 ^ (prefixWord ++ tailWord_5600323).sum := by decide
  have hdescent : baseEnd_5600323 < baseStart_5600323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600334 : List Nat := [4, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2]
def baseStart_5600334 : Nat := 118140960795 + 5600334 * 2 ^ 59
def prefixEnd_5600334 : Nat := 4983230072969 + 3 ^ 40 * 5600334 * 2
def baseEnd_5600334 : Nat := 2875663167716796901169539

theorem tailTrace_5600334 : CollatzResearch.WordTrace tailWord_5600334 prefixEnd_5600334 2875663167716796901169539 := by
  unfold tailWord_5600334
  simp only [CollatzResearch.WordTrace]
  refine ⟨25532620211619231718071007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136173974461969235829712037 25532620211619231718071007)
  ·
    refine ⟨38298930317428847577106511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25532620211619231718071007 38298930317428847577106511)
    ·
      refine ⟨57448395476143271365659767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38298930317428847577106511 57448395476143271365659767)
      ·
        refine ⟨86172593214214907048489651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57448395476143271365659767 86172593214214907048489651)
        ·
          refine ⟨129258889821322360572734477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86172593214214907048489651 129258889821322360572734477)
          ·
            refine ⟨48472083682995885214775429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129258889821322360572734477 48472083682995885214775429)
            ·
              refine ⟨9088515690561728477770393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48472083682995885214775429 9088515690561728477770393)
              ·
                refine ⟨6816386767921296358327795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9088515690561728477770393 6816386767921296358327795)
                ·
                  refine ⟨10224580151881944537491693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6816386767921296358327795 10224580151881944537491693)
                  ·
                    refine ⟨3834217556955729201559385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10224580151881944537491693 3834217556955729201559385)
                    ·
                      refine ⟨2875663167716796901169539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3834217556955729201559385 2875663167716796901169539)
                      ·
                        rfl

theorem cell23_5600334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2].length) (baseStart_5600334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600334 prefixEnd_5600334 := by exact prefixLift 5600334
  have htrace : WordTrace (prefixWord ++ tailWord_5600334) baseStart_5600334 baseEnd_5600334 := by
    simpa [prefixWord, tailWord_5600334, baseEnd_5600334] using wordTrace_append hprefix tailTrace_5600334
  have hstable : (prefixWord ++ tailWord_5600334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600334).length < 2 ^ (prefixWord ++ tailWord_5600334).sum := by decide
  have hdescent : baseEnd_5600334 < baseStart_5600334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600342 : List Nat := [5, 2, 2, 1, 2, 2, 1, 3, 1, 2, 2]
def baseStart_5600342 : Nat := 118140960795 + 5600342 * 2 ^ 59
def prefixEnd_5600342 : Nat := 4983230072969 + 3 ^ 40 * 5600342 * 2
def baseEnd_5600342 : Nat := 2875667275562032869869503

theorem tailTrace_5600342 : CollatzResearch.WordTrace tailWord_5600342 prefixEnd_5600342 2875667275562032869869503 := by
  unfold tailWord_5600342
  simp only [CollatzResearch.WordTrace]
  refine ⟨12766328342307804444428705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136174168984616580740572853 12766328342307804444428705)
  ·
    refine ⟨9574746256730853333321529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12766328342307804444428705 9574746256730853333321529)
    ·
      refine ⟨7181059692548139999991147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9574746256730853333321529 7181059692548139999991147)
      ·
        refine ⟨10771589538822209999986721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7181059692548139999991147 10771589538822209999986721)
        ·
          refine ⟨8078692154116657499990041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10771589538822209999986721 8078692154116657499990041)
          ·
            refine ⟨6059019115587493124992531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8078692154116657499990041 6059019115587493124992531)
            ·
              refine ⟨9088528673381239687488797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6059019115587493124992531 9088528673381239687488797)
              ·
                refine ⟨3408198252517964882808299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9088528673381239687488797 3408198252517964882808299)
                ·
                  refine ⟨5112297378776947324212449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3408198252517964882808299 5112297378776947324212449)
                  ·
                    refine ⟨3834223034082710493159337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5112297378776947324212449 3834223034082710493159337)
                    ·
                      refine ⟨2875667275562032869869503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3834223034082710493159337 2875667275562032869869503)
                      ·
                        rfl

theorem cell23_5600342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_5600342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600342 prefixEnd_5600342 := by exact prefixLift 5600342
  have htrace : WordTrace (prefixWord ++ tailWord_5600342) baseStart_5600342 baseEnd_5600342 := by
    simpa [prefixWord, tailWord_5600342, baseEnd_5600342] using wordTrace_append hprefix tailTrace_5600342
  have hstable : (prefixWord ++ tailWord_5600342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600342).length < 2 ^ (prefixWord ++ tailWord_5600342).sum := by decide
  have hdescent : baseEnd_5600342 < baseStart_5600342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600353 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 9]
def baseStart_5600353 : Nat := 118140960795 + 5600353 * 2 ^ 59
def prefixEnd_5600353 : Nat := 4983230072969 + 3 ^ 40 * 5600353 * 2
def baseEnd_5600353 : Nat := 319519213761025814092439

theorem tailTrace_5600353 : CollatzResearch.WordTrace tailWord_5600353 prefixEnd_5600353 319519213761025814092439 := by
  unfold tailWord_5600353
  simp only [CollatzResearch.WordTrace]
  refine ⟨204261654679885019989509713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136174436453256679993006475 204261654679885019989509713)
  ·
    refine ⟨153196241009913764992132285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204261654679885019989509713 153196241009913764992132285)
    ·
      refine ⟨57448590378717661872049607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153196241009913764992132285 57448590378717661872049607)
      ·
        refine ⟨86172885568076492808074411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57448590378717661872049607 86172885568076492808074411)
        ·
          refine ⟨129259328352114739212111617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86172885568076492808074411 129259328352114739212111617)
          ·
            refine ⟨96944496264086054409083713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129259328352114739212111617 96944496264086054409083713)
            ·
              refine ⟨72708372198064540806812785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96944496264086054409083713 72708372198064540806812785)
              ·
                refine ⟨54531279148548405605109589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72708372198064540806812785 54531279148548405605109589)
                ·
                  refine ⟨319519213761025814092439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54531279148548405605109589 319519213761025814092439)
                  ·
                    rfl

theorem cell23_5600353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 9].length) (baseStart_5600353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600353 prefixEnd_5600353 := by exact prefixLift 5600353
  have htrace : WordTrace (prefixWord ++ tailWord_5600353) baseStart_5600353 baseEnd_5600353 := by
    simpa [prefixWord, tailWord_5600353, baseEnd_5600353] using wordTrace_append hprefix tailTrace_5600353
  have hstable : (prefixWord ++ tailWord_5600353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600353).length < 2 ^ (prefixWord ++ tailWord_5600353).sum := by decide
  have hdescent : baseEnd_5600353 < baseStart_5600353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600364 : List Nat := [2, 2, 1, 1, 3, 2, 2, 4, 2, 2, 2]
def baseStart_5600364 : Nat := 118140960795 + 5600364 * 2 ^ 59
def prefixEnd_5600364 : Nat := 4983230072969 + 3 ^ 40 * 5600364 * 2
def baseEnd_5600364 : Nat := 2875678572136431783794401

theorem tailTrace_5600364 : CollatzResearch.WordTrace tailWord_5600364 prefixEnd_5600364 2875678572136431783794401 := by
  unfold tailWord_5600364
  simp only [CollatzResearch.WordTrace]
  refine ⟨102131027941422584434080073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136174703921896779245440097 102131027941422584434080073)
  ·
    refine ⟨76598270956066938325560055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102131027941422584434080073 76598270956066938325560055)
    ·
      refine ⟨114897406434100407488340083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76598270956066938325560055 114897406434100407488340083)
      ·
        refine ⟨172346109651150611232510125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114897406434100407488340083 172346109651150611232510125)
        ·
          refine ⟨64629791119181479212191297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172346109651150611232510125 64629791119181479212191297)
          ·
            refine ⟨48472343339386109409143473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64629791119181479212191297 48472343339386109409143473)
            ·
              refine ⟨36354257504539582056857605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48472343339386109409143473 36354257504539582056857605)
              ·
                refine ⟨6816423282101171635660801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36354257504539582056857605 6816423282101171635660801)
                ·
                  refine ⟨5112317461575878726745601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6816423282101171635660801 5112317461575878726745601)
                  ·
                    refine ⟨3834238096181909045059201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5112317461575878726745601 3834238096181909045059201)
                    ·
                      refine ⟨2875678572136431783794401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3834238096181909045059201 2875678572136431783794401)
                      ·
                        rfl

theorem cell23_5600364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 2, 2].length) (baseStart_5600364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600364 prefixEnd_5600364 := by exact prefixLift 5600364
  have htrace : WordTrace (prefixWord ++ tailWord_5600364) baseStart_5600364 baseEnd_5600364 := by
    simpa [prefixWord, tailWord_5600364, baseEnd_5600364] using wordTrace_append hprefix tailTrace_5600364
  have hstable : (prefixWord ++ tailWord_5600364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600364).length < 2 ^ (prefixWord ++ tailWord_5600364).sum := by decide
  have hdescent : baseEnd_5600364 < baseStart_5600364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600380 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 1, 5, 3]
def baseStart_5600380 : Nat := 118140960795 + 5600380 * 2 ^ 59
def prefixEnd_5600380 : Nat := 4983230072969 + 3 ^ 40 * 5600380 * 2
def baseEnd_5600380 : Nat := 2875686787826903721194327

theorem tailTrace_5600380 : CollatzResearch.WordTrace tailWord_5600380 prefixEnd_5600380 2875686787826903721194327 := by
  unfold tailWord_5600380
  simp only [CollatzResearch.WordTrace]
  refine ⟨102131319725393601800371297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136175092967191469067161729 102131319725393601800371297)
  ·
    refine ⟨76598489794045201350278473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102131319725393601800371297 76598489794045201350278473)
    ·
      refine ⟨57448867345533901012708855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76598489794045201350278473 57448867345533901012708855)
      ·
        refine ⟨86173301018300851519063283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57448867345533901012708855 86173301018300851519063283)
        ·
          refine ⟨129259951527451277278594925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86173301018300851519063283 129259951527451277278594925)
          ·
            refine ⟨48472481822794228979473097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129259951527451277278594925 48472481822794228979473097)
            ·
              refine ⟨36354361367095671734604823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48472481822794228979473097 36354361367095671734604823)
              ·
                refine ⟨54531542050643507601907235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36354361367095671734604823 54531542050643507601907235)
                ·
                  refine ⟨81797313075965261402860853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54531542050643507601907235 81797313075965261402860853)
                  ·
                    refine ⟨7668498100871743256518205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81797313075965261402860853 7668498100871743256518205)
                    ·
                      refine ⟨2875686787826903721194327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7668498100871743256518205 2875686787826903721194327)
                      ·
                        rfl

theorem cell23_5600380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_5600380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600380 prefixEnd_5600380 := by exact prefixLift 5600380
  have htrace : WordTrace (prefixWord ++ tailWord_5600380) baseStart_5600380 baseEnd_5600380 := by
    simpa [prefixWord, tailWord_5600380, baseEnd_5600380] using wordTrace_append hprefix tailTrace_5600380
  have hstable : (prefixWord ++ tailWord_5600380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600380).length < 2 ^ (prefixWord ++ tailWord_5600380).sum := by decide
  have hdescent : baseEnd_5600380 < baseStart_5600380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600480 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 6]
def baseStart_5600480 : Nat := 118140960795 + 5600480 * 2 ^ 59
def prefixEnd_5600480 : Nat := 4983230072969 + 3 ^ 40 * 5600480 * 2
def baseEnd_5600480 : Nat := 2875738135892353329943867

theorem tailTrace_5600480 : CollatzResearch.WordTrace tailWord_5600480 prefixEnd_5600480 2875738135892353329943867 := by
  unfold tailWord_5600480
  simp only [CollatzResearch.WordTrace]
  refine ⟨102133143375212460339691447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136177524500283280452921929 102133143375212460339691447)
  ·
    refine ⟨153199715062818690509537171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102133143375212460339691447 153199715062818690509537171)
    ·
      refine ⟨229799572594228035764305757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153199715062818690509537171 229799572594228035764305757)
      ·
        refine ⟨86174839722835513411614659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229799572594228035764305757 86174839722835513411614659)
        ·
          refine ⟨129262259584253270117421989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86174839722835513411614659 129262259584253270117421989)
          ·
            refine ⟨24236673672047488147016623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129262259584253270117421989 24236673672047488147016623)
            ·
              refine ⟨36355010508071232220524935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24236673672047488147016623 36355010508071232220524935)
              ·
                refine ⟨54532515762106848330787403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36355010508071232220524935 54532515762106848330787403)
                ·
                  refine ⟨81798773643160272496181105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54532515762106848330787403 81798773643160272496181105)
                  ·
                    refine ⟨61349080232370204372135829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81798773643160272496181105 61349080232370204372135829)
                    ·
                      refine ⟨2875738135892353329943867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61349080232370204372135829 2875738135892353329943867)
                      ·
                        rfl

theorem cell23_5600480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_5600480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600480 prefixEnd_5600480 := by exact prefixLift 5600480
  have htrace : WordTrace (prefixWord ++ tailWord_5600480) baseStart_5600480 baseEnd_5600480 := by
    simpa [prefixWord, tailWord_5600480, baseEnd_5600480] using wordTrace_append hprefix tailTrace_5600480
  have hstable : (prefixWord ++ tailWord_5600480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600480).length < 2 ^ (prefixWord ++ tailWord_5600480).sum := by decide
  have hdescent : baseEnd_5600480 < baseStart_5600480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600547 : List Nat := [1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 5]
def baseStart_5600547 : Nat := 118140960795 + 5600547 * 2 ^ 59
def prefixEnd_5600547 : Nat := 4983230072969 + 3 ^ 40 * 5600547 * 2
def baseEnd_5600547 : Nat := 2875772539096204567806059

theorem tailTrace_5600547 : CollatzResearch.WordTrace tailWord_5600547 prefixEnd_5600547 2875772539096204567806059 := by
  unfold tailWord_5600547
  simp only [CollatzResearch.WordTrace]
  refine ⟨204268730441182191122071895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136179153627454794081381263 204268730441182191122071895)
  ·
    refine ⟨306403095661773286683107843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204268730441182191122071895 306403095661773286683107843)
    ·
      refine ⟨459604643492659930024661765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306403095661773286683107843 459604643492659930024661765)
      ·
        refine ⟨86175870654873736879624081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 459604643492659930024661765 86175870654873736879624081)
        ·
          refine ⟨64631902991155302659718061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86175870654873736879624081 64631902991155302659718061)
          ·
            refine ⟨24236963621683238497394273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64631902991155302659718061 24236963621683238497394273)
            ·
              refine ⟨18177722716262428873045705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24236963621683238497394273 18177722716262428873045705)
              ·
                refine ⟨13633292037196821654784279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18177722716262428873045705 13633292037196821654784279)
                ·
                  refine ⟨20449938055795232482176419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13633292037196821654784279 20449938055795232482176419)
                  ·
                    refine ⟨30674907083692848723264629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20449938055795232482176419 30674907083692848723264629)
                    ·
                      refine ⟨2875772539096204567806059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30674907083692848723264629 2875772539096204567806059)
                      ·
                        rfl

theorem cell23_5600547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_5600547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600547 prefixEnd_5600547 := by exact prefixLift 5600547
  have htrace : WordTrace (prefixWord ++ tailWord_5600547) baseStart_5600547 baseEnd_5600547 := by
    simpa [prefixWord, tailWord_5600547, baseEnd_5600547] using wordTrace_append hprefix tailTrace_5600547
  have hstable : (prefixWord ++ tailWord_5600547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600547).length < 2 ^ (prefixWord ++ tailWord_5600547).sum := by decide
  have hdescent : baseEnd_5600547 < baseStart_5600547 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600561 : List Nat := [1, 2, 2, 3, 3, 3, 1, 2, 1, 1, 4]
def baseStart_5600561 : Nat := 118140960795 + 5600561 * 2 ^ 59
def prefixEnd_5600561 : Nat := 4983230072969 + 3 ^ 40 * 5600561 * 2
def baseEnd_5600561 : Nat := 2875779727825367513030995

theorem tailTrace_5600561 : CollatzResearch.WordTrace tailWord_5600561 prefixEnd_5600561 2875779727825367513030995 := by
  unfold tailWord_5600561
  simp only [CollatzResearch.WordTrace]
  refine ⟨204269241063131471513081537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136179494042087647675387691 204269241063131471513081537)
  ·
    refine ⟨153201930797348603634811153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204269241063131471513081537 153201930797348603634811153)
    ·
      refine ⟨114901448098011452726108365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153201930797348603634811153 114901448098011452726108365)
      ·
        refine ⟨43088043036754294772290637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114901448098011452726108365 43088043036754294772290637)
        ·
          refine ⟨16158016138782860539608989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43088043036754294772290637 16158016138782860539608989)
          ·
            refine ⟨6059256052043572702353371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16158016138782860539608989 6059256052043572702353371)
            ·
              refine ⟨9088884078065359053530057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6059256052043572702353371 9088884078065359053530057)
              ·
                refine ⟨6816663058549019290147543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9088884078065359053530057 6816663058549019290147543)
                ·
                  refine ⟨10224994587823528935221315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6816663058549019290147543 10224994587823528935221315)
                  ·
                    refine ⟨15337491881735293402831973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10224994587823528935221315 15337491881735293402831973)
                    ·
                      refine ⟨2875779727825367513030995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15337491881735293402831973 2875779727825367513030995)
                      ·
                        rfl

theorem cell23_5600561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_5600561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600561 prefixEnd_5600561 := by exact prefixLift 5600561
  have htrace : WordTrace (prefixWord ++ tailWord_5600561) baseStart_5600561 baseEnd_5600561 := by
    simpa [prefixWord, tailWord_5600561, baseEnd_5600561] using wordTrace_append hprefix tailTrace_5600561
  have hstable : (prefixWord ++ tailWord_5600561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600561).length < 2 ^ (prefixWord ++ tailWord_5600561).sum := by decide
  have hdescent : baseEnd_5600561 < baseStart_5600561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600574 : List Nat := [4, 2, 1, 2, 1, 1, 3, 2, 1, 2, 4]
def baseStart_5600574 : Nat := 118140960795 + 5600574 * 2 ^ 59
def prefixEnd_5600574 : Nat := 4983230072969 + 3 ^ 40 * 5600574 * 2
def baseEnd_5600574 : Nat := 2875786403073875962168435

theorem tailTrace_5600574 : CollatzResearch.WordTrace tailWord_5600574 prefixEnd_5600574 2875786403073875962168435 := by
  unfold tailWord_5600574
  simp only [CollatzResearch.WordTrace]
  refine ⟨25533714401510546841663097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136179810141389583155536517 25533714401510546841663097)
  ·
    refine ⟨19150285801132910131247323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25533714401510546841663097 19150285801132910131247323)
    ·
      refine ⟨28725428701699365196870985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19150285801132910131247323 28725428701699365196870985)
      ·
        refine ⟨21544071526274523897653239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28725428701699365196870985 21544071526274523897653239)
        ·
          refine ⟨32316107289411785846479859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21544071526274523897653239 32316107289411785846479859)
          ·
            refine ⟨48474160934117678769719789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32316107289411785846479859 48474160934117678769719789)
            ·
              refine ⟨18177810350294129538644921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48474160934117678769719789 18177810350294129538644921)
              ·
                refine ⟨13633357762720597153983691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18177810350294129538644921 13633357762720597153983691)
                ·
                  refine ⟨20450036644080895730975537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13633357762720597153983691 20450036644080895730975537)
                  ·
                    refine ⟨15337527483060671798231653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20450036644080895730975537 15337527483060671798231653)
                    ·
                      refine ⟨2875786403073875962168435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15337527483060671798231653 2875786403073875962168435)
                      ·
                        rfl

theorem cell23_5600574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_5600574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600574 prefixEnd_5600574 := by exact prefixLift 5600574
  have htrace : WordTrace (prefixWord ++ tailWord_5600574) baseStart_5600574 baseEnd_5600574 := by
    simpa [prefixWord, tailWord_5600574, baseEnd_5600574] using wordTrace_append hprefix tailTrace_5600574
  have hstable : (prefixWord ++ tailWord_5600574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600574).length < 2 ^ (prefixWord ++ tailWord_5600574).sum := by decide
  have hdescent : baseEnd_5600574 < baseStart_5600574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600589 : List Nat := [1, 6, 1, 3, 1, 2, 2, 2, 1, 1, 3]
def baseStart_5600589 : Nat := 118140960795 + 5600589 * 2 ^ 59
def prefixEnd_5600589 : Nat := 4983230072969 + 3 ^ 40 * 5600589 * 2
def baseEnd_5600589 : Nat := 2875794105283693403480867

theorem tailTrace_5600589 : CollatzResearch.WordTrace tailWord_5600589 prefixEnd_5600589 2875794105283693403480867 := by
  unfold tailWord_5600589
  simp only [CollatzResearch.WordTrace]
  refine ⟨204270262307030032295100821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136180174871353354863400547 204270262307030032295100821)
  ·
    refine ⟨9575168545642032763832851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 204270262307030032295100821 9575168545642032763832851)
    ·
      refine ⟨14362752818463049145749277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9575168545642032763832851 14362752818463049145749277)
      ·
        refine ⟨5386032306923643429655979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14362752818463049145749277 5386032306923643429655979)
        ·
          refine ⟨8079048460385465144483969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5386032306923643429655979 8079048460385465144483969)
          ·
            refine ⟨6059286345289098858362977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8079048460385465144483969 6059286345289098858362977)
            ·
              refine ⟨4544464758966824143772233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6059286345289098858362977 4544464758966824143772233)
              ·
                refine ⟨3408348569225118107829175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4544464758966824143772233 3408348569225118107829175)
                ·
                  refine ⟨5112522853837677161743763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3408348569225118107829175 5112522853837677161743763)
                  ·
                    refine ⟨7668784280756515742615645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5112522853837677161743763 7668784280756515742615645)
                    ·
                      refine ⟨2875794105283693403480867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7668784280756515742615645 2875794105283693403480867)
                      ·
                        rfl

theorem cell23_5600589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_5600589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600589 prefixEnd_5600589 := by exact prefixLift 5600589
  have htrace : WordTrace (prefixWord ++ tailWord_5600589) baseStart_5600589 baseEnd_5600589 := by
    simpa [prefixWord, tailWord_5600589, baseEnd_5600589] using wordTrace_append hprefix tailTrace_5600589
  have hstable : (prefixWord ++ tailWord_5600589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600589).length < 2 ^ (prefixWord ++ tailWord_5600589).sum := by decide
  have hdescent : baseEnd_5600589 < baseStart_5600589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600597 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 2, 7]
def baseStart_5600597 : Nat := 118140960795 + 5600597 * 2 ^ 59
def prefixEnd_5600597 : Nat := 4983230072969 + 3 ^ 40 * 5600597 * 2
def baseEnd_5600597 : Nat := 958599404376309790726943

theorem tailTrace_5600597 : CollatzResearch.WordTrace tailWord_5600597 prefixEnd_5600597 958599404376309790726943 := by
  unfold tailWord_5600597
  simp only [CollatzResearch.WordTrace]
  refine ⟨204270554091001049661392045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136180369394000699774261363 204270554091001049661392045)
  ·
    refine ⟨76601457784125393623022017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204270554091001049661392045 76601457784125393623022017)
    ·
      refine ⟨57451093338094045217266513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76601457784125393623022017 57451093338094045217266513)
      ·
        refine ⟨43088320003570533912949885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57451093338094045217266513 43088320003570533912949885)
        ·
          refine ⟨16158120001338950217356207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43088320003570533912949885 16158120001338950217356207)
          ·
            refine ⟨24237180002008425326034311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16158120001338950217356207 24237180002008425326034311)
            ·
              refine ⟨36355770003012637989051467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24237180002008425326034311 36355770003012637989051467)
              ·
                refine ⟨54533655004518956983577201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36355770003012637989051467 54533655004518956983577201)
                ·
                  refine ⟨40900241253389217737682901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54533655004518956983577201 40900241253389217737682901)
                  ·
                    refine ⟨958599404376309790726943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40900241253389217737682901 958599404376309790726943)
                    ·
                      rfl

theorem cell23_5600597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_5600597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600597 prefixEnd_5600597 := by exact prefixLift 5600597
  have htrace : WordTrace (prefixWord ++ tailWord_5600597) baseStart_5600597 baseEnd_5600597 := by
    simpa [prefixWord, tailWord_5600597, baseEnd_5600597] using wordTrace_append hprefix tailTrace_5600597
  have hstable : (prefixWord ++ tailWord_5600597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600597).length < 2 ^ (prefixWord ++ tailWord_5600597).sum := by decide
  have hdescent : baseEnd_5600597 < baseStart_5600597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600611 : List Nat := [1, 1, 1, 5, 2, 2, 2, 3, 2, 1, 3]
def baseStart_5600611 : Nat := 118140960795 + 5600611 * 2 ^ 59
def prefixEnd_5600611 : Nat := 4983230072969 + 3 ^ 40 * 5600611 * 2
def baseEnd_5600611 : Nat := 2875805401858092317405765

theorem tailTrace_5600611 : CollatzResearch.WordTrace tailWord_5600611 prefixEnd_5600611 2875805401858092317405765 := by
  unfold tailWord_5600611
  simp only [CollatzResearch.WordTrace]
  refine ⟨204271064712950330052401687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136180709808633553368267791 204271064712950330052401687)
  ·
    refine ⟨306406597069425495078602531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204271064712950330052401687 306406597069425495078602531)
    ·
      refine ⟨459609895604138242617903797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306406597069425495078602531 459609895604138242617903797)
      ·
        refine ⟨43088427712887960245428481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 459609895604138242617903797 43088427712887960245428481)
        ·
          refine ⟨32316320784665970184071361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43088427712887960245428481 32316320784665970184071361)
          ·
            refine ⟨24237240588499477638053521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32316320784665970184071361 24237240588499477638053521)
            ·
              refine ⟨18177930441374608228540141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24237240588499477638053521 18177930441374608228540141)
              ·
                refine ⟨6816723915515478085702553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18177930441374608228540141 6816723915515478085702553)
                ·
                  refine ⟨5112542936636608564276915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6816723915515478085702553 5112542936636608564276915)
                  ·
                    refine ⟨7668814404954912846415373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5112542936636608564276915 7668814404954912846415373)
                    ·
                      refine ⟨2875805401858092317405765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7668814404954912846415373 2875805401858092317405765)
                      ·
                        rfl

theorem cell23_5600611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_5600611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600611 prefixEnd_5600611 := by exact prefixLift 5600611
  have htrace : WordTrace (prefixWord ++ tailWord_5600611) baseStart_5600611 baseEnd_5600611 := by
    simpa [prefixWord, tailWord_5600611, baseEnd_5600611] using wordTrace_append hprefix tailTrace_5600611
  have hstable : (prefixWord ++ tailWord_5600611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600611).length < 2 ^ (prefixWord ++ tailWord_5600611).sum := by decide
  have hdescent : baseEnd_5600611 < baseStart_5600611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600621 : List Nat := [1, 5, 1, 1, 1, 3, 2, 1, 3, 3, 2]
def baseStart_5600621 : Nat := 118140960795 + 5600621 * 2 ^ 59
def prefixEnd_5600621 : Nat := 4983230072969 + 3 ^ 40 * 5600621 * 2
def baseEnd_5600621 : Nat := 2875810536664637278280719

theorem tailTrace_5600621 : CollatzResearch.WordTrace tailWord_5600621 prefixEnd_5600621 2875810536664637278280719 := by
  unfold tailWord_5600621
  simp only [CollatzResearch.WordTrace]
  refine ⟨204271429442914101760265717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136180952961942734506843811 204271429442914101760265717)
  ·
    refine ⟨19150446510273197040024911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 204271429442914101760265717 19150446510273197040024911)
    ·
      refine ⟨28725669765409795560037367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19150446510273197040024911 28725669765409795560037367)
      ·
        refine ⟨43088504648114693340056051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28725669765409795560037367 43088504648114693340056051)
        ·
          refine ⟨64632756972172040010084077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43088504648114693340056051 64632756972172040010084077)
          ·
            refine ⟨24237283864564515003781529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64632756972172040010084077 24237283864564515003781529)
            ·
              refine ⟨18177962898423386252836147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24237283864564515003781529 18177962898423386252836147)
              ·
                refine ⟨27266944347635079379254221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18177962898423386252836147 27266944347635079379254221)
                ·
                  refine ⟨10225104130363154767220333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27266944347635079379254221 10225104130363154767220333)
                  ·
                    refine ⟨3834414048886183037707625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10225104130363154767220333 3834414048886183037707625)
                    ·
                      refine ⟨2875810536664637278280719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3834414048886183037707625 2875810536664637278280719)
                      ·
                        rfl

theorem cell23_5600621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_5600621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600621 prefixEnd_5600621 := by exact prefixLift 5600621
  have htrace : WordTrace (prefixWord ++ tailWord_5600621) baseStart_5600621 baseEnd_5600621 := by
    simpa [prefixWord, tailWord_5600621, baseEnd_5600621] using wordTrace_append hprefix tailTrace_5600621
  have hstable : (prefixWord ++ tailWord_5600621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600621).length < 2 ^ (prefixWord ++ tailWord_5600621).sum := by decide
  have hdescent : baseEnd_5600621 < baseStart_5600621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600637 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 1, 3, 5]
def baseStart_5600637 : Nat := 118140960795 + 5600637 * 2 ^ 59
def prefixEnd_5600637 : Nat := 4983230072969 + 3 ^ 40 * 5600637 * 2
def baseEnd_5600637 : Nat := 2875818752355109215680645

theorem tailTrace_5600637 : CollatzResearch.WordTrace tailWord_5600637 prefixEnd_5600637 2875818752355109215680645 := by
  unfold tailWord_5600637
  simp only [CollatzResearch.WordTrace]
  refine ⟨204272013010856136492848165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136181342007237424328565443 204272013010856136492848165)
  ·
    refine ⟨38301002439535525592409031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204272013010856136492848165 38301002439535525592409031)
    ·
      refine ⟨57451503659303288388613547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38301002439535525592409031 57451503659303288388613547)
      ·
        refine ⟨86177255488954932582920321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57451503659303288388613547 86177255488954932582920321)
        ·
          refine ⟨64632941616716199437190241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86177255488954932582920321 64632941616716199437190241)
          ·
            refine ⟨48474706212537149577892681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64632941616716199437190241 48474706212537149577892681)
            ·
              refine ⟨36356029659402862183419511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48474706212537149577892681 36356029659402862183419511)
              ·
                refine ⟨54534044489104293275129267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36356029659402862183419511 54534044489104293275129267)
                ·
                  refine ⟨81801066733656439912693901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54534044489104293275129267 81801066733656439912693901)
                  ·
                    refine ⟨30675400025121164967260213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81801066733656439912693901 30675400025121164967260213)
                    ·
                      refine ⟨2875818752355109215680645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30675400025121164967260213 2875818752355109215680645)
                      ·
                        rfl

theorem cell23_5600637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_5600637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600637 prefixEnd_5600637 := by exact prefixLift 5600637
  have htrace : WordTrace (prefixWord ++ tailWord_5600637) baseStart_5600637 baseEnd_5600637 := by
    simpa [prefixWord, tailWord_5600637, baseEnd_5600637] using wordTrace_append hprefix tailTrace_5600637
  have hstable : (prefixWord ++ tailWord_5600637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600637).length < 2 ^ (prefixWord ++ tailWord_5600637).sum := by decide
  have hdescent : baseEnd_5600637 < baseStart_5600637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600651 : List Nat := [1, 1, 1, 1, 4, 3, 3, 1, 4, 2, 2]
def baseStart_5600651 : Nat := 118140960795 + 5600651 * 2 ^ 59
def prefixEnd_5600651 : Nat := 4983230072969 + 3 ^ 40 * 5600651 * 2
def baseEnd_5600651 : Nat := 2875825941084272160905581

theorem tailTrace_5600651 : CollatzResearch.WordTrace tailWord_5600651 prefixEnd_5600651 2875825941084272160905581 := by
  unfold tailWord_5600651
  simp only [CollatzResearch.WordTrace]
  refine ⟨204272523632805416883857807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136181682421870277922571871 204272523632805416883857807)
  ·
    refine ⟨306408785449208125325786711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204272523632805416883857807 306408785449208125325786711)
    ·
      refine ⟨459613178173812187988680067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306408785449208125325786711 459613178173812187988680067)
      ·
        refine ⟨689419767260718281983020101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459613178173812187988680067 689419767260718281983020101)
        ·
          refine ⟨129266206361384677871816269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 689419767260718281983020101 129266206361384677871816269)
          ·
            refine ⟨48474827385519254201931101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129266206361384677871816269 48474827385519254201931101)
            ·
              refine ⟨18178060269569720325724163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48474827385519254201931101 18178060269569720325724163)
              ·
                refine ⟨27267090404354580488586245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18178060269569720325724163 27267090404354580488586245)
                ·
                  refine ⟨5112579450816483841609921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27267090404354580488586245 5112579450816483841609921)
                  ·
                    refine ⟨3834434588112362881207441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5112579450816483841609921 3834434588112362881207441)
                    ·
                      refine ⟨2875825941084272160905581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3834434588112362881207441 2875825941084272160905581)
                      ·
                        rfl

theorem cell23_5600651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 4, 2, 2].length) (baseStart_5600651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600651 prefixEnd_5600651 := by exact prefixLift 5600651
  have htrace : WordTrace (prefixWord ++ tailWord_5600651) baseStart_5600651 baseEnd_5600651 := by
    simpa [prefixWord, tailWord_5600651, baseEnd_5600651] using wordTrace_append hprefix tailTrace_5600651
  have hstable : (prefixWord ++ tailWord_5600651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600651).length < 2 ^ (prefixWord ++ tailWord_5600651).sum := by decide
  have hdescent : baseEnd_5600651 < baseStart_5600651 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600674 : List Nat := [3, 3, 1, 2, 1, 2, 2, 2, 7]
def baseStart_5600674 : Nat := 118140960795 + 5600674 * 2 ^ 59
def prefixEnd_5600674 : Nat := 4983230072969 + 3 ^ 40 * 5600674 * 2
def baseEnd_5600674 : Nat := 319537527904369507879775

theorem tailTrace_5600674 : CollatzResearch.WordTrace tailWord_5600674 prefixEnd_5600674 319537527904369507879775 := by
  unfold tailWord_5600674
  simp only [CollatzResearch.WordTrace]
  refine ⟨51068340627930522952986269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136182241674481394541296717 51068340627930522952986269)
  ·
    refine ⟨19150627735473946107369851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51068340627930522952986269 19150627735473946107369851)
    ·
      refine ⟨28725941603210919161054777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19150627735473946107369851 28725941603210919161054777)
      ·
        refine ⟨21544456202408189370791083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28725941603210919161054777 21544456202408189370791083)
        ·
          refine ⟨32316684303612284056186625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21544456202408189370791083 32316684303612284056186625)
          ·
            refine ⟨24237513227709213042139969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32316684303612284056186625 24237513227709213042139969)
            ·
              refine ⟨18178134920781909781604977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24237513227709213042139969 18178134920781909781604977)
              ·
                refine ⟨13633601190586432336203733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18178134920781909781604977 13633601190586432336203733)
                ·
                  refine ⟨319537527904369507879775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13633601190586432336203733 319537527904369507879775)
                  ·
                    rfl

theorem cell23_5600674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_5600674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600674 prefixEnd_5600674 := by exact prefixLift 5600674
  have htrace : WordTrace (prefixWord ++ tailWord_5600674) baseStart_5600674 baseEnd_5600674 := by
    simpa [prefixWord, tailWord_5600674, baseEnd_5600674] using wordTrace_append hprefix tailTrace_5600674
  have hstable : (prefixWord ++ tailWord_5600674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600674).length < 2 ^ (prefixWord ++ tailWord_5600674).sum := by decide
  have hdescent : baseEnd_5600674 < baseStart_5600674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600687 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 6, 5]
def baseStart_5600687 : Nat := 118140960795 + 5600687 * 2 ^ 59
def prefixEnd_5600687 : Nat := 4983230072969 + 3 ^ 40 * 5600687 * 2
def baseEnd_5600687 : Nat := 958614808795944673351805

theorem tailTrace_5600687 : CollatzResearch.WordTrace tailWord_5600687 prefixEnd_5600687 958614808795944673351805 := by
  unfold tailWord_5600687
  simp only [CollatzResearch.WordTrace]
  refine ⟨204273836660674995032168315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136182557773783330021445543 204273836660674995032168315)
  ·
    refine ⟨306410754991012492548252473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204273836660674995032168315 306410754991012492548252473)
    ·
      refine ⟨229808066243259369411189355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306410754991012492548252473 229808066243259369411189355)
      ·
        refine ⟨344712099364889054116784033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229808066243259369411189355 344712099364889054116784033)
        ·
          refine ⟨258534074523666790587588025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344712099364889054116784033 258534074523666790587588025)
          ·
            refine ⟨193900555892750092940691019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258534074523666790587588025 193900555892750092940691019)
            ·
              refine ⟨290850833839125139411036529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193900555892750092940691019 290850833839125139411036529)
              ·
                refine ⟨218138125379343854558277397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290850833839125139411036529 218138125379343854558277397)
                ·
                  refine ⟨10225224627156743182419253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 218138125379343854558277397 10225224627156743182419253)
                  ·
                    refine ⟨958614808795944673351805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10225224627156743182419253 958614808795944673351805)
                    ·
                      rfl

theorem cell23_5600687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 5].length) (baseStart_5600687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600687 prefixEnd_5600687 := by exact prefixLift 5600687
  have htrace : WordTrace (prefixWord ++ tailWord_5600687) baseStart_5600687 baseEnd_5600687 := by
    simpa [prefixWord, tailWord_5600687, baseEnd_5600687] using wordTrace_append hprefix tailTrace_5600687
  have hstable : (prefixWord ++ tailWord_5600687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600687).length < 2 ^ (prefixWord ++ tailWord_5600687).sum := by decide
  have hdescent : baseEnd_5600687 < baseStart_5600687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600714 : List Nat := [3, 1, 2, 1, 2, 4, 1, 1, 1, 2, 5]
def baseStart_5600714 : Nat := 118140960795 + 5600714 * 2 ^ 59
def prefixEnd_5600714 : Nat := 4983230072969 + 3 ^ 40 * 5600714 * 2
def baseEnd_5600714 : Nat := 2875858290365505414417791

theorem tailTrace_5600714 : CollatzResearch.WordTrace tailWord_5600714 prefixEnd_5600714 2875858290365505414417791 := by
  unfold tailWord_5600714
  simp only [CollatzResearch.WordTrace]
  refine ⟨51068705357894294660850299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136183214287718119095600797 51068705357894294660850299)
  ·
    refine ⟨76603058036841441991275449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51068705357894294660850299 76603058036841441991275449)
    ·
      refine ⟨57452293527631081493456587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76603058036841441991275449 57452293527631081493456587)
      ·
        refine ⟨86178440291446622240184881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57452293527631081493456587 86178440291446622240184881)
        ·
          refine ⟨64633830218584966680138661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86178440291446622240184881 64633830218584966680138661)
          ·
            refine ⟨12118843165984681252525999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64633830218584966680138661 12118843165984681252525999)
            ·
              refine ⟨18178264748977021878788999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12118843165984681252525999 18178264748977021878788999)
              ·
                refine ⟨27267397123465532818183499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18178264748977021878788999 27267397123465532818183499)
                ·
                  refine ⟨40901095685198299227275249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27267397123465532818183499 40901095685198299227275249)
                  ·
                    refine ⟨30675821763898724420456437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40901095685198299227275249 30675821763898724420456437)
                    ·
                      refine ⟨2875858290365505414417791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30675821763898724420456437 2875858290365505414417791)
                      ·
                        rfl

theorem cell23_5600714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_5600714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600714 prefixEnd_5600714 := by exact prefixLift 5600714
  have htrace : WordTrace (prefixWord ++ tailWord_5600714) baseStart_5600714 baseEnd_5600714 := by
    simpa [prefixWord, tailWord_5600714, baseEnd_5600714] using wordTrace_append hprefix tailTrace_5600714
  have hstable : (prefixWord ++ tailWord_5600714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600714).length < 2 ^ (prefixWord ++ tailWord_5600714).sum := by decide
  have hdescent : baseEnd_5600714 < baseStart_5600714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600727 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 5]
def baseStart_5600727 : Nat := 118140960795 + 5600727 * 2 ^ 59
def prefixEnd_5600727 : Nat := 4983230072969 + 3 ^ 40 * 5600727 * 2
def baseEnd_5600727 : Nat := 2875864965614013863555231

theorem tailTrace_5600727 : CollatzResearch.WordTrace tailWord_5600727 prefixEnd_5600727 2875864965614013863555231 := by
  unfold tailWord_5600727
  simp only [CollatzResearch.WordTrace]
  refine ⟨204275295580530081863624435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136183530387020054575749623 204275295580530081863624435)
  ·
    refine ⟨306412943370795122795436653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204275295580530081863624435 306412943370795122795436653)
    ·
      refine ⟨114904853764048171048288745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306412943370795122795436653 114904853764048171048288745)
      ·
        refine ⟨86178640323036128286216559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114904853764048171048288745 86178640323036128286216559)
        ·
          refine ⟨129267960484554192429324839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86178640323036128286216559 129267960484554192429324839)
          ·
            refine ⟨193901940726831288643987259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129267960484554192429324839 193901940726831288643987259)
            ·
              refine ⟨290852911090246932965980889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193901940726831288643987259 290852911090246932965980889)
              ·
                refine ⟨218139683317685199724485667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290852911090246932965980889 218139683317685199724485667)
                ·
                  refine ⟨327209524976527799586728501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218139683317685199724485667 327209524976527799586728501)
                  ·
                    refine ⟨30675892966549481211255797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 327209524976527799586728501 30675892966549481211255797)
                    ·
                      refine ⟨2875864965614013863555231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30675892966549481211255797 2875864965614013863555231)
                      ·
                        rfl

theorem cell23_5600727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_5600727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600727 prefixEnd_5600727 := by exact prefixLift 5600727
  have htrace : WordTrace (prefixWord ++ tailWord_5600727) baseStart_5600727 baseEnd_5600727 := by
    simpa [prefixWord, tailWord_5600727, baseEnd_5600727] using wordTrace_append hprefix tailTrace_5600727
  have hstable : (prefixWord ++ tailWord_5600727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600727).length < 2 ^ (prefixWord ++ tailWord_5600727).sum := by decide
  have hdescent : baseEnd_5600727 < baseStart_5600727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600741 : List Nat := [1, 3, 1, 5, 1, 1, 1, 3, 2, 1, 4]
def baseStart_5600741 : Nat := 118140960795 + 5600741 * 2 ^ 59
def prefixEnd_5600741 : Nat := 4983230072969 + 3 ^ 40 * 5600741 * 2
def baseEnd_5600741 : Nat := 2875872154343176808780167

theorem tailTrace_5600741 : CollatzResearch.WordTrace tailWord_5600741 prefixEnd_5600741 2875872154343176808780167 := by
  unfold tailWord_5600741
  simp only [CollatzResearch.WordTrace]
  refine ⟨204275806202479362254634077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136183870801652908169756051 204275806202479362254634077)
  ·
    refine ⟨76603427325929760845487779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204275806202479362254634077 76603427325929760845487779)
    ·
      refine ⟨114905140988894641268231669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76603427325929760845487779 114905140988894641268231669)
      ·
        refine ⟨10772356967708872618896719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 114905140988894641268231669 10772356967708872618896719)
        ·
          refine ⟨16158535451563308928345079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10772356967708872618896719 16158535451563308928345079)
          ·
            refine ⟨24237803177344963392517619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16158535451563308928345079 24237803177344963392517619)
            ·
              refine ⟨36356704766017445088776429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24237803177344963392517619 36356704766017445088776429)
              ·
                refine ⟨13633764287256541908291161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36356704766017445088776429 13633764287256541908291161)
                ·
                  refine ⟨10225323215442406431218371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13633764287256541908291161 10225323215442406431218371)
                  ·
                    refine ⟨15337984823163609646827557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10225323215442406431218371 15337984823163609646827557)
                    ·
                      refine ⟨2875872154343176808780167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15337984823163609646827557 2875872154343176808780167)
                      ·
                        rfl

theorem cell23_5600741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_5600741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600741 prefixEnd_5600741 := by exact prefixLift 5600741
  have htrace : WordTrace (prefixWord ++ tailWord_5600741) baseStart_5600741 baseEnd_5600741 := by
    simpa [prefixWord, tailWord_5600741, baseEnd_5600741] using wordTrace_append hprefix tailTrace_5600741
  have hstable : (prefixWord ++ tailWord_5600741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600741).length < 2 ^ (prefixWord ++ tailWord_5600741).sum := by decide
  have hdescent : baseEnd_5600741 < baseStart_5600741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600747 : List Nat := [1, 1, 1, 1, 2, 3, 2, 4, 8]
def baseStart_5600747 : Nat := 118140960795 + 5600747 * 2 ^ 59
def prefixEnd_5600747 : Nat := 4983230072969 + 3 ^ 40 * 5600747 * 2
def baseEnd_5600747 : Nat := 319541692803011531700571

theorem tailTrace_5600747 : CollatzResearch.WordTrace tailWord_5600747 prefixEnd_5600747 319541692803011531700571 := by
  unfold tailWord_5600747
  simp only [CollatzResearch.WordTrace]
  refine ⟨204276025040457625279352495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136184016693638416852901663 204276025040457625279352495)
  ·
    refine ⟨306414037560686437919028743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204276025040457625279352495 306414037560686437919028743)
    ·
      refine ⟨459621056341029656878543115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306414037560686437919028743 459621056341029656878543115)
      ·
        refine ⟨689431584511544485317814673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459621056341029656878543115 689431584511544485317814673)
        ·
          refine ⟨517073688383658363988361005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 689431584511544485317814673 517073688383658363988361005)
          ·
            refine ⟨193902633143871886495635377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 517073688383658363988361005 193902633143871886495635377)
            ·
              refine ⟨145426974857903914871726533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193902633143871886495635377 145426974857903914871726533)
              ·
                refine ⟨27267557785856984038448725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145426974857903914871726533 27267557785856984038448725)
                ·
                  refine ⟨319541692803011531700571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27267557785856984038448725 319541692803011531700571)
                  ·
                    rfl

theorem cell23_5600747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 8].length) (baseStart_5600747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600747 prefixEnd_5600747 := by exact prefixLift 5600747
  have htrace : WordTrace (prefixWord ++ tailWord_5600747) baseStart_5600747 baseEnd_5600747 := by
    simpa [prefixWord, tailWord_5600747, baseEnd_5600747] using wordTrace_append hprefix tailTrace_5600747
  have hstable : (prefixWord ++ tailWord_5600747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600747).length < 2 ^ (prefixWord ++ tailWord_5600747).sum := by decide
  have hdescent : baseEnd_5600747 < baseStart_5600747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600764 : List Nat := [2, 2, 2, 1, 2, 1, 3, 4, 6]
def baseStart_5600764 : Nat := 118140960795 + 5600764 * 2 ^ 59
def prefixEnd_5600764 : Nat := 4983230072969 + 3 ^ 40 * 5600764 * 2
def baseEnd_5600764 : Nat := 319542662710914468754729

theorem tailTrace_5600764 : CollatzResearch.WordTrace tailWord_5600764 prefixEnd_5600764 319542662710914468754729 := by
  unfold tailWord_5600764
  simp only [CollatzResearch.WordTrace]
  refine ⟨102138322540698018591360673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136184430054264024788480897 102138322540698018591360673)
  ·
    refine ⟨76603741905523513943520505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102138322540698018591360673 76603741905523513943520505)
    ·
      refine ⟨57452806429142635457640379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76603741905523513943520505 57452806429142635457640379)
      ·
        refine ⟨86179209643713953186460569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57452806429142635457640379 86179209643713953186460569)
        ·
          refine ⟨64634407232785464889845427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86179209643713953186460569 64634407232785464889845427)
          ·
            refine ⟨96951610849178197334768141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64634407232785464889845427 96951610849178197334768141)
            ·
              refine ⟨36356854068441824000538053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96951610849178197334768141 36356854068441824000538053)
              ·
                refine ⟨6816910137832842000100885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36356854068441824000538053 6816910137832842000100885)
                ·
                  refine ⟨319542662710914468754729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6816910137832842000100885 319542662710914468754729)
                  ·
                    rfl

theorem cell23_5600764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 6].length) (baseStart_5600764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600764 prefixEnd_5600764 := by exact prefixLift 5600764
  have htrace : WordTrace (prefixWord ++ tailWord_5600764) baseStart_5600764 baseEnd_5600764 := by
    simpa [prefixWord, tailWord_5600764, baseEnd_5600764] using wordTrace_append hprefix tailTrace_5600764
  have hstable : (prefixWord ++ tailWord_5600764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600764).length < 2 ^ (prefixWord ++ tailWord_5600764).sum := by decide
  have hdescent : baseEnd_5600764 < baseStart_5600764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600825 : List Nat := [1, 2, 1, 5, 1, 2, 2, 4, 1, 1, 3]
def baseStart_5600825 : Nat := 118140960795 + 5600825 * 2 ^ 59
def prefixEnd_5600825 : Nat := 4983230072969 + 3 ^ 40 * 5600825 * 2
def baseEnd_5600825 : Nat := 2875915286718154480129781

theorem tailTrace_5600825 : CollatzResearch.WordTrace tailWord_5600825 prefixEnd_5600825 2875915286718154480129781 := by
  unfold tailWord_5600825
  simp only [CollatzResearch.WordTrace]
  refine ⟨204278869934175044600691929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136185913289450029733794619 204278869934175044600691929)
  ·
    refine ⟨153209152450631283450518947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204278869934175044600691929 153209152450631283450518947)
    ·
      refine ⟨229813728675946925175778421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153209152450631283450518947 229813728675946925175778421)
      ·
        refine ⟨21545037063370024235229227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 229813728675946925175778421 21545037063370024235229227)
        ·
          refine ⟨32317555595055036352843841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21545037063370024235229227 32317555595055036352843841)
          ·
            refine ⟨24238166696291277264632881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32317555595055036352843841 24238166696291277264632881)
            ·
              refine ⟨18178625022218457948474661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24238166696291277264632881 18178625022218457948474661)
              ·
                refine ⟨3408492191665960865338999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18178625022218457948474661 3408492191665960865338999)
                ·
                  refine ⟨5112738287498941298008499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3408492191665960865338999 5112738287498941298008499)
                  ·
                    refine ⟨7669107431248411947012749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5112738287498941298008499 7669107431248411947012749)
                    ·
                      refine ⟨2875915286718154480129781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7669107431248411947012749 2875915286718154480129781)
                      ·
                        rfl

theorem cell23_5600825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_5600825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600825 prefixEnd_5600825 := by exact prefixLift 5600825
  have htrace : WordTrace (prefixWord ++ tailWord_5600825) baseStart_5600825 baseEnd_5600825 := by
    simpa [prefixWord, tailWord_5600825, baseEnd_5600825] using wordTrace_append hprefix tailTrace_5600825
  have hstable : (prefixWord ++ tailWord_5600825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600825).length < 2 ^ (prefixWord ++ tailWord_5600825).sum := by decide
  have hdescent : baseEnd_5600825 < baseStart_5600825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600841 : List Nat := [1, 2, 1, 1, 2, 2, 1, 7, 2, 4]
def baseStart_5600841 : Nat := 118140960795 + 5600841 * 2 ^ 59
def prefixEnd_5600841 : Nat := 4983230072969 + 3 ^ 40 * 5600841 * 2
def baseEnd_5600841 : Nat := 958641167469542139176569

theorem tailTrace_5600841 : CollatzResearch.WordTrace tailWord_5600841 prefixEnd_5600841 958641167469542139176569 := by
  unfold tailWord_5600841
  simp only [CollatzResearch.WordTrace]
  refine ⟨204279453502117079333274377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136186302334744719555516251 204279453502117079333274377)
  ·
    refine ⟨153209590126587809499955783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204279453502117079333274377 153209590126587809499955783)
    ·
      refine ⟨229814385189881714249933675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153209590126587809499955783 229814385189881714249933675)
      ·
        refine ⟨344721577784822571374900513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229814385189881714249933675 344721577784822571374900513)
        ·
          refine ⟨258541183338616928531175385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344721577784822571374900513 258541183338616928531175385)
          ·
            refine ⟨193905887503962696398381539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258541183338616928531175385 193905887503962696398381539)
            ·
              refine ⟨290858831255944044597572309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193905887503962696398381539 290858831255944044597572309)
              ·
                refine ⟨6817003857561188545255601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 290858831255944044597572309 6817003857561188545255601)
                ·
                  refine ⟨5112752893170891408941701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6817003857561188545255601 5112752893170891408941701)
                  ·
                    refine ⟨958641167469542139176569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5112752893170891408941701 958641167469542139176569)
                    ·
                      rfl

theorem cell23_5600841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 2, 4].length) (baseStart_5600841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600841 prefixEnd_5600841 := by exact prefixLift 5600841
  have htrace : WordTrace (prefixWord ++ tailWord_5600841) baseStart_5600841 baseEnd_5600841 := by
    simpa [prefixWord, tailWord_5600841, baseEnd_5600841] using wordTrace_append hprefix tailTrace_5600841
  have hstable : (prefixWord ++ tailWord_5600841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600841).length < 2 ^ (prefixWord ++ tailWord_5600841).sum := by decide
  have hdescent : baseEnd_5600841 < baseStart_5600841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600845 : List Nat := [1, 6, 1, 1, 3, 1, 2, 2, 1, 5]
def baseStart_5600845 : Nat := 118140960795 + 5600845 * 2 ^ 59
def prefixEnd_5600845 : Nat := 4983230072969 + 3 ^ 40 * 5600845 * 2
def baseEnd_5600845 : Nat := 958641852110414800626563

theorem tailTrace_5600845 : CollatzResearch.WordTrace tailWord_5600845 prefixEnd_5600845 958641852110414800626563 := by
  unfold tailWord_5600845
  simp only [CollatzResearch.WordTrace]
  refine ⟨204279599394102588016419989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136186399596068392010946659 204279599394102588016419989)
  ·
    refine ⟨9575606221598558813269687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 204279599394102588016419989 9575606221598558813269687)
    ·
      refine ⟨14363409332397838219904531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9575606221598558813269687 14363409332397838219904531)
      ·
        refine ⟨21545113998596757329856797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14363409332397838219904531 21545113998596757329856797)
        ·
          refine ⟨8079417749473783998696299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21545113998596757329856797 8079417749473783998696299)
          ·
            refine ⟨12119126624210675998044449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8079417749473783998696299 12119126624210675998044449)
            ·
              refine ⟨9089344968158006998533337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12119126624210675998044449 9089344968158006998533337)
              ·
                refine ⟨6817008726118505248900003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9089344968158006998533337 6817008726118505248900003)
                ·
                  refine ⟨10225513089177757873350005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6817008726118505248900003 10225513089177757873350005)
                  ·
                    refine ⟨958641852110414800626563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10225513089177757873350005 958641852110414800626563)
                    ·
                      rfl

theorem cell23_5600845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_5600845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600845 prefixEnd_5600845 := by exact prefixLift 5600845
  have htrace : WordTrace (prefixWord ++ tailWord_5600845) baseStart_5600845 baseEnd_5600845 := by
    simpa [prefixWord, tailWord_5600845, baseEnd_5600845] using wordTrace_append hprefix tailTrace_5600845
  have hstable : (prefixWord ++ tailWord_5600845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600845).length < 2 ^ (prefixWord ++ tailWord_5600845).sum := by decide
  have hdescent : baseEnd_5600845 < baseStart_5600845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600848 : List Nat := [2, 1, 1, 1, 1, 3, 3, 4, 3, 2, 2]
def baseStart_5600848 : Nat := 118140960795 + 5600848 * 2 ^ 59
def prefixEnd_5600848 : Nat := 4983230072969 + 3 ^ 40 * 5600848 * 2
def baseEnd_5600848 : Nat := 2875927096773207890142175

theorem tailTrace_5600848 : CollatzResearch.WordTrace tailWord_5600848 prefixEnd_5600848 2875927096773207890142175 := by
  unfold tailWord_5600848
  simp only [CollatzResearch.WordTrace]
  refine ⟨102139854406545859764389599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136186472542061146352519465 102139854406545859764389599)
  ·
    refine ⟨153209781609818789646584399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102139854406545859764389599 153209781609818789646584399)
    ·
      refine ⟨229814672414728184469876599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153209781609818789646584399 229814672414728184469876599)
      ·
        refine ⟨344722008622092276704814899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229814672414728184469876599 344722008622092276704814899)
        ·
          refine ⟨517083012933138415057222349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344722008622092276704814899 517083012933138415057222349)
          ·
            refine ⟨193906129849926905646458381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 517083012933138415057222349 193906129849926905646458381)
            ·
              refine ⟨72714798693722589617421893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193906129849926905646458381 72714798693722589617421893)
              ·
                refine ⟨13634024755072985553266605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72714798693722589617421893 13634024755072985553266605)
                ·
                  refine ⟨5112759283152369582474977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13634024755072985553266605 5112759283152369582474977)
                  ·
                    refine ⟨3834569462364277186856233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5112759283152369582474977 3834569462364277186856233)
                    ·
                      refine ⟨2875927096773207890142175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3834569462364277186856233 2875927096773207890142175)
                      ·
                        rfl

theorem cell23_5600848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 3, 2, 2].length) (baseStart_5600848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600848 prefixEnd_5600848 := by exact prefixLift 5600848
  have htrace : WordTrace (prefixWord ++ tailWord_5600848) baseStart_5600848 baseEnd_5600848 := by
    simpa [prefixWord, tailWord_5600848, baseEnd_5600848] using wordTrace_append hprefix tailTrace_5600848
  have hstable : (prefixWord ++ tailWord_5600848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600848).length < 2 ^ (prefixWord ++ tailWord_5600848).sum := by decide
  have hdescent : baseEnd_5600848 < baseStart_5600848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600868 : List Nat := [2, 3, 1, 1, 2, 3, 2, 3, 1, 2, 3]
def baseStart_5600868 : Nat := 118140960795 + 5600868 * 2 ^ 59
def prefixEnd_5600868 : Nat := 4983230072969 + 3 ^ 40 * 5600868 * 2
def baseEnd_5600868 : Nat := 2875937366386297811892083

theorem tailTrace_5600868 : CollatzResearch.WordTrace tailWord_5600868 prefixEnd_5600868 2875937366386297811892083 := by
  unfold tailWord_5600868
  simp only [CollatzResearch.WordTrace]
  refine ⟨102140219136509631472253629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136186958848679508629671505 102140219136509631472253629)
  ·
    refine ⟨38302582176191111802095111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102140219136509631472253629 38302582176191111802095111)
    ·
      refine ⟨57453873264286667703142667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38302582176191111802095111 57453873264286667703142667)
      ·
        refine ⟨86180809896430001554714001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57453873264286667703142667 86180809896430001554714001)
        ·
          refine ⟨64635607422322501166035501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86180809896430001554714001 64635607422322501166035501)
          ·
            refine ⟨24238352783370937937263313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64635607422322501166035501 24238352783370937937263313)
            ·
              refine ⟨18178764587528203452947485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24238352783370937937263313 18178764587528203452947485)
              ·
                refine ⟨6817036720323076294855307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18178764587528203452947485 6817036720323076294855307)
                ·
                  refine ⟨10225555080484614442282961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6817036720323076294855307 10225555080484614442282961)
                  ·
                    refine ⟨7669166310363460831712221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10225555080484614442282961 7669166310363460831712221)
                    ·
                      refine ⟨2875937366386297811892083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7669166310363460831712221 2875937366386297811892083)
                      ·
                        rfl

theorem cell23_5600868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_5600868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600868 prefixEnd_5600868 := by exact prefixLift 5600868
  have htrace : WordTrace (prefixWord ++ tailWord_5600868) baseStart_5600868 baseEnd_5600868 := by
    simpa [prefixWord, tailWord_5600868, baseEnd_5600868] using wordTrace_append hprefix tailTrace_5600868
  have hstable : (prefixWord ++ tailWord_5600868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600868).length < 2 ^ (prefixWord ++ tailWord_5600868).sum := by decide
  have hdescent : baseEnd_5600868 < baseStart_5600868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600882 : List Nat := [3, 2, 1, 2, 3, 3, 1, 1, 3, 2, 2]
def baseStart_5600882 : Nat := 118140960795 + 5600882 * 2 ^ 59
def prefixEnd_5600882 : Nat := 4983230072969 + 3 ^ 40 * 5600882 * 2
def baseEnd_5600882 : Nat := 2875944555115460757117019

theorem tailTrace_5600882 : CollatzResearch.WordTrace tailWord_5600882 prefixEnd_5600882 2875944555115460757117019 := by
  unfold tailWord_5600882
  simp only [CollatzResearch.WordTrace]
  refine ⟨51070237223742135833879225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136187299263312362223677933 51070237223742135833879225)
  ·
    refine ⟨38302677917806601875409419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51070237223742135833879225 38302677917806601875409419)
    ·
      refine ⟨57454016876709902813114129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38302677917806601875409419 57454016876709902813114129)
      ·
        refine ⟨43090512657532427109835597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57454016876709902813114129 43090512657532427109835597)
        ·
          refine ⟨16158942246574660166188349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43090512657532427109835597 16158942246574660166188349)
          ·
            refine ⟨6059603342465497562320631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16158942246574660166188349 6059603342465497562320631)
            ·
              refine ⟨9089405013698246343480947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6059603342465497562320631 9089405013698246343480947)
              ·
                refine ⟨13634107520547369515221421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9089405013698246343480947 13634107520547369515221421)
                ·
                  refine ⟨5112790320205263568208033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13634107520547369515221421 5112790320205263568208033)
                  ·
                    refine ⟨3834592740153947676156025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5112790320205263568208033 3834592740153947676156025)
                    ·
                      refine ⟨2875944555115460757117019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3834592740153947676156025 2875944555115460757117019)
                      ·
                        rfl

theorem cell23_5600882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_5600882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600882 prefixEnd_5600882 := by exact prefixLift 5600882
  have htrace : WordTrace (prefixWord ++ tailWord_5600882) baseStart_5600882 baseEnd_5600882 := by
    simpa [prefixWord, tailWord_5600882, baseEnd_5600882] using wordTrace_append hprefix tailTrace_5600882
  have hstable : (prefixWord ++ tailWord_5600882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600882).length < 2 ^ (prefixWord ++ tailWord_5600882).sum := by decide
  have hdescent : baseEnd_5600882 < baseStart_5600882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600908 : List Nat := [2, 2, 1, 2, 1, 1, 5, 1, 3, 3, 2]
def baseStart_5600908 : Nat := 118140960795 + 5600908 * 2 ^ 59
def prefixEnd_5600908 : Nat := 4983230072969 + 3 ^ 40 * 5600908 * 2
def baseEnd_5600908 : Nat := 2875957905612477655391899

theorem tailTrace_5600908 : CollatzResearch.WordTrace tailWord_5600908 prefixEnd_5600908 2875957905612477655391899 := by
  unfold tailWord_5600908
  simp only [CollatzResearch.WordTrace]
  refine ⟨102140948596437174887981689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136187931461916233183975585 102140948596437174887981689)
  ·
    refine ⟨76605711447327881165986267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102140948596437174887981689 76605711447327881165986267)
    ·
      refine ⟨114908567170991821748979401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76605711447327881165986267 114908567170991821748979401)
      ·
        refine ⟨86181425378243866311734551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114908567170991821748979401 86181425378243866311734551)
        ·
          refine ⟨129272138067365799467601827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86181425378243866311734551 129272138067365799467601827)
          ·
            refine ⟨193908207101048699201402741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129272138067365799467601827 193908207101048699201402741)
            ·
              refine ⟨18178894415723315550131507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 193908207101048699201402741 18178894415723315550131507)
              ·
                refine ⟨27268341623584973325197261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18178894415723315550131507 27268341623584973325197261)
                ·
                  refine ⟨10225628108844364996948973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27268341623584973325197261 10225628108844364996948973)
                  ·
                    refine ⟨3834610540816636873855865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10225628108844364996948973 3834610540816636873855865)
                    ·
                      refine ⟨2875957905612477655391899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3834610540816636873855865 2875957905612477655391899)
                      ·
                        rfl

theorem cell23_5600908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 3, 3, 2].length) (baseStart_5600908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600908 prefixEnd_5600908 := by exact prefixLift 5600908
  have htrace : WordTrace (prefixWord ++ tailWord_5600908) baseStart_5600908 baseEnd_5600908 := by
    simpa [prefixWord, tailWord_5600908, baseEnd_5600908] using wordTrace_append hprefix tailTrace_5600908
  have hstable : (prefixWord ++ tailWord_5600908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600908).length < 2 ^ (prefixWord ++ tailWord_5600908).sum := by decide
  have hdescent : baseEnd_5600908 < baseStart_5600908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600951 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 4]
def baseStart_5600951 : Nat := 118140960795 + 5600951 * 2 ^ 59
def prefixEnd_5600951 : Nat := 4983230072969 + 3 ^ 40 * 5600951 * 2
def baseEnd_5600951 : Nat := 2875979985280620987154201

theorem tailTrace_5600951 : CollatzResearch.WordTrace tailWord_5600951 prefixEnd_5600951 2875979985280620987154201 := by
  unfold tailWord_5600951
  simp only [CollatzResearch.WordTrace]
  refine ⟨204283465531718568119778707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136188977021145712079852471 204283465531718568119778707)
  ·
    refine ⟨306425198297577852179668061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204283465531718568119778707 306425198297577852179668061)
    ·
      refine ⟨114909449361591694567375523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306425198297577852179668061 114909449361591694567375523)
      ·
        refine ⟨172364174042387541851063285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114909449361591694567375523 172364174042387541851063285)
        ·
          refine ⟨16159141316473832048537183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 172364174042387541851063285 16159141316473832048537183)
          ·
            refine ⟨24238711974710748072805775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16159141316473832048537183 24238711974710748072805775)
            ·
              refine ⟨36358067962066122109208663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24238711974710748072805775 36358067962066122109208663)
              ·
                refine ⟨54537101943099183163812995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36358067962066122109208663 54537101943099183163812995)
                ·
                  refine ⟨81805652914648774745719493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54537101943099183163812995 81805652914648774745719493)
                  ·
                    refine ⟨15338559921496645264822405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81805652914648774745719493 15338559921496645264822405)
                    ·
                      refine ⟨2875979985280620987154201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15338559921496645264822405 2875979985280620987154201)
                      ·
                        rfl

theorem cell23_5600951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_5600951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600951 prefixEnd_5600951 := by exact prefixLift 5600951
  have htrace : WordTrace (prefixWord ++ tailWord_5600951) baseStart_5600951 baseEnd_5600951 := by
    simpa [prefixWord, tailWord_5600951, baseEnd_5600951] using wordTrace_append hprefix tailTrace_5600951
  have hstable : (prefixWord ++ tailWord_5600951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600951).length < 2 ^ (prefixWord ++ tailWord_5600951).sum := by decide
  have hdescent : baseEnd_5600951 < baseStart_5600951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600989 : List Nat := [1, 4, 3, 3, 1, 1, 1, 1, 4, 2, 2]
def baseStart_5600989 : Nat := 118140960795 + 5600989 * 2 ^ 59
def prefixEnd_5600989 : Nat := 4983230072969 + 3 ^ 40 * 5600989 * 2
def baseEnd_5600989 : Nat := 2875999497545491838479027

theorem tailTrace_5600989 : CollatzResearch.WordTrace tailWord_5600989 prefixEnd_5600989 2875999497545491838479027 := by
  unfold tailWord_5600989
  simp only [CollatzResearch.WordTrace]
  refine ⟨204284851505580900609662021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136189901003720600406441347 204284851505580900609662021)
  ·
    refine ⟨38303409657296418864311629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204284851505580900609662021 38303409657296418864311629)
    ·
      refine ⟨14363778621486157074116861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38303409657296418864311629 14363778621486157074116861)
      ·
        refine ⟨5386416983057308902793823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14363778621486157074116861 5386416983057308902793823)
        ·
          refine ⟨8079625474585963354190735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5386416983057308902793823 8079625474585963354190735)
          ·
            refine ⟨12119438211878945031286103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8079625474585963354190735 12119438211878945031286103)
            ·
              refine ⟨18179157317818417546929155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12119438211878945031286103 18179157317818417546929155)
              ·
                refine ⟨27268735976727626320393733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18179157317818417546929155 27268735976727626320393733)
                ·
                  refine ⟨5112887995636429935073825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27268735976727626320393733 5112887995636429935073825)
                  ·
                    refine ⟨3834665996727322451305369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5112887995636429935073825 3834665996727322451305369)
                    ·
                      refine ⟨2875999497545491838479027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3834665996727322451305369 2875999497545491838479027)
                      ·
                        rfl

theorem cell23_5600989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_5600989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600989 prefixEnd_5600989 := by exact prefixLift 5600989
  have htrace : WordTrace (prefixWord ++ tailWord_5600989) baseStart_5600989 baseEnd_5600989 := by
    simpa [prefixWord, tailWord_5600989, baseEnd_5600989] using wordTrace_append hprefix tailTrace_5600989
  have hstable : (prefixWord ++ tailWord_5600989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600989).length < 2 ^ (prefixWord ++ tailWord_5600989).sum := by decide
  have hdescent : baseEnd_5600989 < baseStart_5600989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5600991 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 4, 5]
def baseStart_5600991 : Nat := 118140960795 + 5600991 * 2 ^ 59
def prefixEnd_5600991 : Nat := 4983230072969 + 3 ^ 40 * 5600991 * 2
def baseEnd_5600991 : Nat := 958666841502266943551339

theorem tailTrace_5600991 : CollatzResearch.WordTrace tailWord_5600991 prefixEnd_5600991 958666841502266943551339 := by
  unfold tailWord_5600991
  simp only [CollatzResearch.WordTrace]
  refine ⟨204284924451573654951234827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136189949634382436634156551 204284924451573654951234827)
  ·
    refine ⟨306427386677360482426852241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204284924451573654951234827 306427386677360482426852241)
    ·
      refine ⟨229820540008020361820139181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306427386677360482426852241 229820540008020361820139181)
      ·
        refine ⟨86182702503007635682552193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229820540008020361820139181 86182702503007635682552193)
        ·
          refine ⟨64637026877255726761914145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86182702503007635682552193 64637026877255726761914145)
          ·
            refine ⟨48477770157941795071435609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64637026877255726761914145 48477770157941795071435609)
            ·
              refine ⟨36358327618456346303576707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48477770157941795071435609 36358327618456346303576707)
              ·
                refine ⟨54537491427684519455365061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36358327618456346303576707 54537491427684519455365061)
                ·
                  refine ⟨10225779642690847397880949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54537491427684519455365061 10225779642690847397880949)
                  ·
                    refine ⟨958666841502266943551339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10225779642690847397880949 958666841502266943551339)
                    ·
                      rfl

theorem cell23_5600991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 5].length) (baseStart_5600991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5600991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5600991 prefixEnd_5600991 := by exact prefixLift 5600991
  have htrace : WordTrace (prefixWord ++ tailWord_5600991) baseStart_5600991 baseEnd_5600991 := by
    simpa [prefixWord, tailWord_5600991, baseEnd_5600991] using wordTrace_append hprefix tailTrace_5600991
  have hstable : (prefixWord ++ tailWord_5600991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5600991).length < 2 ^ (prefixWord ++ tailWord_5600991).sum := by decide
  have hdescent : baseEnd_5600991 < baseStart_5600991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5600991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601011 : List Nat := [1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 4]
def baseStart_5601011 : Nat := 118140960795 + 5601011 * 2 ^ 59
def prefixEnd_5601011 : Nat := 4983230072969 + 3 ^ 40 * 5601011 * 2
def baseEnd_5601011 : Nat := 2876010794119890752403925

theorem tailTrace_5601011 : CollatzResearch.WordTrace tailWord_5601011 prefixEnd_5601011 2876010794119890752403925 := by
  unfold tailWord_5601011
  simp only [CollatzResearch.WordTrace]
  refine ⟨204285653911501198366962887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136190435941000798911308591 204285653911501198366962887)
  ·
    refine ⟨306428480867251797550444331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204285653911501198366962887 306428480867251797550444331)
    ·
      refine ⟨459642721300877696325666497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306428480867251797550444331 459642721300877696325666497)
      ·
        refine ⟨344732040975658272244249873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 459642721300877696325666497 344732040975658272244249873)
        ·
          refine ⟨258549030731743704183187405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344732040975658272244249873 258549030731743704183187405)
          ·
            refine ⟨96955886524403889068695277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 258549030731743704183187405 96955886524403889068695277)
            ·
              refine ⟨36358457446651458400760729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96955886524403889068695277 36358457446651458400760729)
              ·
                refine ⟨27268843084988593800570547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36358457446651458400760729 27268843084988593800570547)
                ·
                  refine ⟨40903264627482890700855821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27268843084988593800570547 40903264627482890700855821)
                  ·
                    refine ⟨15338724235306084012820933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40903264627482890700855821 15338724235306084012820933)
                    ·
                      refine ⟨2876010794119890752403925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15338724235306084012820933 2876010794119890752403925)
                      ·
                        rfl

theorem cell23_5601011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 4].length) (baseStart_5601011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601011 prefixEnd_5601011 := by exact prefixLift 5601011
  have htrace : WordTrace (prefixWord ++ tailWord_5601011) baseStart_5601011 baseEnd_5601011 := by
    simpa [prefixWord, tailWord_5601011, baseEnd_5601011] using wordTrace_append hprefix tailTrace_5601011
  have hstable : (prefixWord ++ tailWord_5601011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601011).length < 2 ^ (prefixWord ++ tailWord_5601011).sum := by decide
  have hdescent : baseEnd_5601011 < baseStart_5601011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601028 : List Nat := [2, 3, 2, 2, 1, 2, 2, 1, 1, 3, 4]
def baseStart_5601028 : Nat := 118140960795 + 5601028 * 2 ^ 59
def prefixEnd_5601028 : Nat := 4983230072969 + 3 ^ 40 * 5601028 * 2
def baseEnd_5601028 : Nat := 2876019523291017185891347

theorem tailTrace_5601028 : CollatzResearch.WordTrace tailWord_5601028 prefixEnd_5601028 2876019523291017185891347 := by
  unfold tailWord_5601028
  simp only [CollatzResearch.WordTrace]
  refine ⟨102143136976219805135165869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136190849301626406846887825 102143136976219805135165869)
  ·
    refine ⟨38303676366082426925687201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102143136976219805135165869 38303676366082426925687201)
    ·
      refine ⟨28727757274561820194265401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38303676366082426925687201 28727757274561820194265401)
      ·
        refine ⟨21545817955921365145699051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28727757274561820194265401 21545817955921365145699051)
        ·
          refine ⟨32318726933882047718548577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21545817955921365145699051 32318726933882047718548577)
          ·
            refine ⟨24239045200411535788911433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32318726933882047718548577 24239045200411535788911433)
            ·
              refine ⟨18179283900308651841683575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24239045200411535788911433 18179283900308651841683575)
              ·
                refine ⟨27268925850462977762525363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18179283900308651841683575 27268925850462977762525363)
                ·
                  refine ⟨40903388775694466643788045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27268925850462977762525363 40903388775694466643788045)
                  ·
                    refine ⟨15338770790885424991420517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40903388775694466643788045 15338770790885424991420517)
                    ·
                      refine ⟨2876019523291017185891347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15338770790885424991420517 2876019523291017185891347)
                      ·
                        rfl

theorem cell23_5601028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_5601028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601028 prefixEnd_5601028 := by exact prefixLift 5601028
  have htrace : WordTrace (prefixWord ++ tailWord_5601028) baseStart_5601028 baseEnd_5601028 := by
    simpa [prefixWord, tailWord_5601028, baseEnd_5601028] using wordTrace_append hprefix tailTrace_5601028
  have hstable : (prefixWord ++ tailWord_5601028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601028).length < 2 ^ (prefixWord ++ tailWord_5601028).sum := by decide
  have hdescent : baseEnd_5601028 < baseStart_5601028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601038 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 5, 4]
def baseStart_5601038 : Nat := 118140960795 + 5601038 * 2 ^ 59
def prefixEnd_5601038 : Nat := 4983230072969 + 3 ^ 40 * 5601038 * 2
def baseEnd_5601038 : Nat := 958674886032520715588767

theorem tailTrace_5601038 : CollatzResearch.WordTrace tailWord_5601038 prefixEnd_5601038 958674886032520715588767 := by
  unfold tailWord_5601038
  simp only [CollatzResearch.WordTrace]
  refine ⟨25535829835300422747274471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136191092454935587985463845 25535829835300422747274471)
  ·
    refine ⟨38303744752950634120911707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25535829835300422747274471 38303744752950634120911707)
    ·
      refine ⟨57455617129425951181367561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38303744752950634120911707 57455617129425951181367561)
      ·
        refine ⟨43091712847069463386025671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57455617129425951181367561 43091712847069463386025671)
        ·
          refine ⟨64637569270604195079038507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43091712847069463386025671 64637569270604195079038507)
          ·
            refine ⟨96956353905906292618557761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64637569270604195079038507 96956353905906292618557761)
            ·
              refine ⟨72717265429429719463918321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96956353905906292618557761 72717265429429719463918321)
              ·
                refine ⟨54537949072072289597938741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72717265429429719463918321 54537949072072289597938741)
                ·
                  refine ⟨5112932725506777149806757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54537949072072289597938741 5112932725506777149806757)
                  ·
                    refine ⟨958674886032520715588767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5112932725506777149806757 958674886032520715588767)
                    ·
                      rfl

theorem cell23_5601038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_5601038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601038 prefixEnd_5601038 := by exact prefixLift 5601038
  have htrace : WordTrace (prefixWord ++ tailWord_5601038) baseStart_5601038 baseEnd_5601038 := by
    simpa [prefixWord, tailWord_5601038, baseEnd_5601038] using wordTrace_append hprefix tailTrace_5601038
  have hstable : (prefixWord ++ tailWord_5601038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601038).length < 2 ^ (prefixWord ++ tailWord_5601038).sum := by decide
  have hdescent : baseEnd_5601038 < baseStart_5601038 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601048 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 4, 2, 3]
def baseStart_5601048 : Nat := 118140960795 + 5601048 * 2 ^ 59
def prefixEnd_5601048 : Nat := 4983230072969 + 3 ^ 40 * 5601048 * 2
def baseEnd_5601048 : Nat := 2876029792904107107641255

theorem tailTrace_5601048 : CollatzResearch.WordTrace tailWord_5601048 prefixEnd_5601048 2876029792904107107641255 := by
  unfold tailWord_5601048
  simp only [CollatzResearch.WordTrace]
  refine ⟨102143501706183576843029899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136191335608244769124039865 102143501706183576843029899)
  ·
    refine ⟨153215252559275365264544849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102143501706183576843029899 153215252559275365264544849)
    ·
      refine ⟨114911439419456523948408637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153215252559275365264544849 114911439419456523948408637)
      ·
        refine ⟨43091789782296196480653239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114911439419456523948408637 43091789782296196480653239)
        ·
          refine ⟨64637684673444294720979859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43091789782296196480653239 64637684673444294720979859)
          ·
            refine ⟨96956527010166442081469789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64637684673444294720979859 96956527010166442081469789)
            ·
              refine ⟨36358697628812415780551171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96956527010166442081469789 36358697628812415780551171)
              ·
                refine ⟨54538046443218623670826757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36358697628812415780551171 54538046443218623670826757)
                ·
                  refine ⟨10225883708103491938280017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54538046443218623670826757 10225883708103491938280017)
                  ·
                    refine ⟨7669412781077618953710013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10225883708103491938280017 7669412781077618953710013)
                    ·
                      refine ⟨2876029792904107107641255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7669412781077618953710013 2876029792904107107641255)
                      ·
                        rfl

theorem cell23_5601048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_5601048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601048 prefixEnd_5601048 := by exact prefixLift 5601048
  have htrace : WordTrace (prefixWord ++ tailWord_5601048) baseStart_5601048 baseEnd_5601048 := by
    simpa [prefixWord, tailWord_5601048, baseEnd_5601048] using wordTrace_append hprefix tailTrace_5601048
  have hstable : (prefixWord ++ tailWord_5601048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601048).length < 2 ^ (prefixWord ++ tailWord_5601048).sum := by decide
  have hdescent : baseEnd_5601048 < baseStart_5601048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601068 : List Nat := [2, 2, 1, 1, 1, 6, 1, 3, 6]
def baseStart_5601068 : Nat := 118140960795 + 5601068 * 2 ^ 59
def prefixEnd_5601068 : Nat := 4983230072969 + 3 ^ 40 * 5601068 * 2
def baseEnd_5601068 : Nat := 319560006946355225487907

theorem tailTrace_5601068 : CollatzResearch.WordTrace tailWord_5601068 prefixEnd_5601068 319560006946355225487907 := by
  unfold tailWord_5601068
  simp only [CollatzResearch.WordTrace]
  refine ⟨102143866436147348550893929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136191821914863131401191905 102143866436147348550893929)
  ·
    refine ⟨76607899827110511413170447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102143866436147348550893929 76607899827110511413170447)
    ·
      refine ⟨114911849740665767119755671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76607899827110511413170447 114911849740665767119755671)
      ·
        refine ⟨172367774610998650679633507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114911849740665767119755671 172367774610998650679633507)
        ·
          refine ⟨258551661916497976019450261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172367774610998650679633507 258551661916497976019450261)
          ·
            refine ⟨12119609152335842625911731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 258551661916497976019450261 12119609152335842625911731)
            ·
              refine ⟨18179413728503763938867597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12119609152335842625911731 18179413728503763938867597)
              ·
                refine ⟨6817280148188911477075349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18179413728503763938867597 6817280148188911477075349)
                ·
                  refine ⟨319560006946355225487907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6817280148188911477075349 319560006946355225487907)
                  ·
                    rfl

theorem cell23_5601068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 6].length) (baseStart_5601068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601068 prefixEnd_5601068 := by exact prefixLift 5601068
  have htrace : WordTrace (prefixWord ++ tailWord_5601068) baseStart_5601068 baseEnd_5601068 := by
    simpa [prefixWord, tailWord_5601068, baseEnd_5601068] using wordTrace_append hprefix tailTrace_5601068
  have hstable : (prefixWord ++ tailWord_5601068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601068).length < 2 ^ (prefixWord ++ tailWord_5601068).sum := by decide
  have hdescent : baseEnd_5601068 < baseStart_5601068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601162 : List Nat := [3, 1, 2, 4, 2, 1, 1, 1, 4, 4]
def baseStart_5601162 : Nat := 118140960795 + 5601162 * 2 ^ 59
def prefixEnd_5601162 : Nat := 4983230072969 + 3 ^ 40 * 5601162 * 2
def baseEnd_5601162 : Nat := 958696109899573220538577

theorem tailTrace_5601162 : CollatzResearch.WordTrace tailWord_5601162 prefixEnd_5601162 958696109899573220538577 := by
  unfold tailWord_5601162
  simp only [CollatzResearch.WordTrace]
  refine ⟨51072790333488537788927435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136194107555969434103806493 51072790333488537788927435)
  ·
    refine ⟨76609185500232806683391153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51072790333488537788927435 76609185500232806683391153)
    ·
      refine ⟨57456889125174605012543365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76609185500232806683391153 57456889125174605012543365)
      ·
        refine ⟨10773166710970238439851881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57456889125174605012543365 10773166710970238439851881)
        ·
          refine ⟨8079875033227678829888911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10773166710970238439851881 8079875033227678829888911)
          ·
            refine ⟨12119812549841518244833367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8079875033227678829888911 12119812549841518244833367)
            ·
              refine ⟨18179718824762277367250051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12119812549841518244833367 18179718824762277367250051)
              ·
                refine ⟨27269578237143416050875077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18179718824762277367250051 27269578237143416050875077)
                ·
                  refine ⟨5113045919464390509539077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27269578237143416050875077 5113045919464390509539077)
                  ·
                    refine ⟨958696109899573220538577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5113045919464390509539077 958696109899573220538577)
                    ·
                      rfl

theorem cell23_5601162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_5601162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601162 prefixEnd_5601162 := by exact prefixLift 5601162
  have htrace : WordTrace (prefixWord ++ tailWord_5601162) baseStart_5601162 baseEnd_5601162 := by
    simpa [prefixWord, tailWord_5601162, baseEnd_5601162] using wordTrace_append hprefix tailTrace_5601162
  have hstable : (prefixWord ++ tailWord_5601162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601162).length < 2 ^ (prefixWord ++ tailWord_5601162).sum := by decide
  have hdescent : baseEnd_5601162 < baseStart_5601162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601168 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 3]
def baseStart_5601168 : Nat := 118140960795 + 5601168 * 2 ^ 59
def prefixEnd_5601168 : Nat := 4983230072969 + 3 ^ 40 * 5601168 * 2
def baseEnd_5601168 : Nat := 2876091410582646638140703

theorem tailTrace_5601168 : CollatzResearch.WordTrace tailWord_5601168 prefixEnd_5601168 2876091410582646638140703 := by
  unfold tailWord_5601168
  simp only [CollatzResearch.WordTrace]
  refine ⟨102145690085966207090214079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136194253447954942786952105 102145690085966207090214079)
  ·
    refine ⟨153218535128949310635321119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102145690085966207090214079 153218535128949310635321119)
    ·
      refine ⟨229827802693423965952981679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153218535128949310635321119 229827802693423965952981679)
      ·
        refine ⟨344741704040135948929472519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229827802693423965952981679 344741704040135948929472519)
        ·
          refine ⟨517112556060203923394208779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344741704040135948929472519 517112556060203923394208779)
          ·
            refine ⟨775668834090305885091313169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 517112556060203923394208779 775668834090305885091313169)
            ·
              refine ⟨581751625567729413818484877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 775668834090305885091313169 581751625567729413818484877)
              ·
                refine ⟨218156859587898530181931829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 581751625567729413818484877 218156859587898530181931829)
                ·
                  refine ⟨20452205586365487204556109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 218156859587898530181931829 20452205586365487204556109)
                  ·
                    refine ⟨7669577094887057701708541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20452205586365487204556109 7669577094887057701708541)
                    ·
                      refine ⟨2876091410582646638140703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7669577094887057701708541 2876091410582646638140703)
                      ·
                        rfl

theorem cell23_5601168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 3].length) (baseStart_5601168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601168 prefixEnd_5601168 := by exact prefixLift 5601168
  have htrace : WordTrace (prefixWord ++ tailWord_5601168) baseStart_5601168 baseEnd_5601168 := by
    simpa [prefixWord, tailWord_5601168, baseEnd_5601168] using wordTrace_append hprefix tailTrace_5601168
  have hstable : (prefixWord ++ tailWord_5601168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601168).length < 2 ^ (prefixWord ++ tailWord_5601168).sum := by decide
  have hdescent : baseEnd_5601168 < baseStart_5601168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601169 : List Nat := [1, 2, 2, 1, 1, 1, 6, 4, 1, 2, 2]
def baseStart_5601169 : Nat := 118140960795 + 5601169 * 2 ^ 59
def prefixEnd_5601169 : Nat := 4983230072969 + 3 ^ 40 * 5601169 * 2
def baseEnd_5601169 : Nat := 2876091924063301134228199

theorem tailTrace_5601169 : CollatzResearch.WordTrace tailWord_5601169 prefixEnd_5601169 2876091924063301134228199 := by
  unfold tailWord_5601169
  simp only [CollatzResearch.WordTrace]
  refine ⟨204291416644928791351214561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136194277763285860900809707 204291416644928791351214561)
  ·
    refine ⟨153218562483696593513410921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204291416644928791351214561 153218562483696593513410921)
    ·
      refine ⟨114913921862772445135058191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153218562483696593513410921 114913921862772445135058191)
      ·
        refine ⟨172370882794158667702587287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114913921862772445135058191 172370882794158667702587287)
        ·
          refine ⟨258556324191238001553880931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172370882794158667702587287 258556324191238001553880931)
          ·
            refine ⟨387834486286857002330821397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258556324191238001553880931 387834486286857002330821397)
            ·
              refine ⟨18179741544696421984257253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 387834486286857002330821397 18179741544696421984257253)
              ·
                refine ⟨3408701539630579122048235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18179741544696421984257253 3408701539630579122048235)
                ·
                  refine ⟨5113052309445868683072353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3408701539630579122048235 5113052309445868683072353)
                  ·
                    refine ⟨3834789232084401512304265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5113052309445868683072353 3834789232084401512304265)
                    ·
                      refine ⟨2876091924063301134228199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3834789232084401512304265 2876091924063301134228199)
                      ·
                        rfl

theorem cell23_5601169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 4, 1, 2, 2].length) (baseStart_5601169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601169 prefixEnd_5601169 := by exact prefixLift 5601169
  have htrace : WordTrace (prefixWord ++ tailWord_5601169) baseStart_5601169 baseEnd_5601169 := by
    simpa [prefixWord, tailWord_5601169, baseEnd_5601169] using wordTrace_append hprefix tailTrace_5601169
  have hstable : (prefixWord ++ tailWord_5601169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601169).length < 2 ^ (prefixWord ++ tailWord_5601169).sum := by decide
  have hdescent : baseEnd_5601169 < baseStart_5601169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601192 : List Nat := [2, 1, 6, 2, 1, 1, 1, 9]
def baseStart_5601192 : Nat := 118140960795 + 5601192 * 2 ^ 59
def prefixEnd_5601192 : Nat := 4983230072969 + 3 ^ 40 * 5601192 * 2
def baseEnd_5601192 : Nat := 106522360522902020157059

theorem tailTrace_5601192 : CollatzResearch.WordTrace tailWord_5601192 prefixEnd_5601192 106522360522902020157059 := by
  unfold tailWord_5601192
  simp only [CollatzResearch.WordTrace]
  refine ⟨102146127761922733139650915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136194837015896977519534553 102146127761922733139650915)
  ·
    refine ⟨153219191642884099709476373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102146127761922733139650915 153219191642884099709476373)
    ·
      refine ⟨7182149608260192173881705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 153219191642884099709476373 7182149608260192173881705)
      ·
        refine ⟨5386612206195144130411279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7182149608260192173881705 5386612206195144130411279)
        ·
          refine ⟨8079918309292716195616919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5386612206195144130411279 8079918309292716195616919)
          ·
            refine ⟨12119877463939074293425379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8079918309292716195616919 12119877463939074293425379)
            ·
              refine ⟨18179816195908611440138069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12119877463939074293425379 18179816195908611440138069)
              ·
                refine ⟨106522360522902020157059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18179816195908611440138069 106522360522902020157059)
                ·
                  rfl

theorem cell23_5601192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 9].length) (baseStart_5601192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601192 prefixEnd_5601192 := by exact prefixLift 5601192
  have htrace : WordTrace (prefixWord ++ tailWord_5601192) baseStart_5601192 baseEnd_5601192 := by
    simpa [prefixWord, tailWord_5601192, baseEnd_5601192] using wordTrace_append hprefix tailTrace_5601192
  have hstable : (prefixWord ++ tailWord_5601192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601192).length < 2 ^ (prefixWord ++ tailWord_5601192).sum := by decide
  have hdescent : baseEnd_5601192 < baseStart_5601192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601225 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 3, 4, 2]
def baseStart_5601225 : Nat := 118140960795 + 5601225 * 2 ^ 59
def prefixEnd_5601225 : Nat := 4983230072969 + 3 ^ 40 * 5601225 * 2
def baseEnd_5601225 : Nat := 2876120678979952915127941

theorem tailTrace_5601225 : CollatzResearch.WordTrace tailWord_5601225 prefixEnd_5601225 2876120678979952915127941 := by
  unfold tailWord_5601225
  simp only [CollatzResearch.WordTrace]
  refine ⟨204293459132725912915253129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136195639421817275276835419 204293459132725912915253129)
  ·
    refine ⟨153220094349544434686439847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204293459132725912915253129 153220094349544434686439847)
    ·
      refine ⟨229830141524316652029659771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153220094349544434686439847 229830141524316652029659771)
      ·
        refine ⟨344745212286474978044489657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229830141524316652029659771 344745212286474978044489657)
        ·
          refine ⟨258558909214856233533367243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344745212286474978044489657 258558909214856233533367243)
          ·
            refine ⟨387838363822284350300050865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258558909214856233533367243 387838363822284350300050865)
            ·
              refine ⟨290878772866713262725038149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 387838363822284350300050865 290878772866713262725038149)
              ·
                refine ⟨54539769912508736760944653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 290878772866713262725038149 54539769912508736760944653)
                ·
                  refine ⟨20452413717190776285354245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54539769912508736760944653 20452413717190776285354245)
                  ·
                    refine ⟨3834827571973270553503921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20452413717190776285354245 3834827571973270553503921)
                    ·
                      refine ⟨2876120678979952915127941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3834827571973270553503921 2876120678979952915127941)
                      ·
                        rfl

theorem cell23_5601225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 4, 2].length) (baseStart_5601225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601225 prefixEnd_5601225 := by exact prefixLift 5601225
  have htrace : WordTrace (prefixWord ++ tailWord_5601225) baseStart_5601225 baseEnd_5601225 := by
    simpa [prefixWord, tailWord_5601225, baseEnd_5601225] using wordTrace_append hprefix tailTrace_5601225
  have hstable : (prefixWord ++ tailWord_5601225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601225).length < 2 ^ (prefixWord ++ tailWord_5601225).sum := by decide
  have hdescent : baseEnd_5601225 < baseStart_5601225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601248 : List Nat := [2, 1, 1, 3, 1, 1, 1, 6, 7]
def baseStart_5601248 : Nat := 118140960795 + 5601248 * 2 ^ 59
def prefixEnd_5601248 : Nat := 4983230072969 + 3 ^ 40 * 5601248 * 2
def baseEnd_5601248 : Nat := 319570276559445147237815

theorem tailTrace_5601248 : CollatzResearch.WordTrace tailWord_5601248 prefixEnd_5601248 319570276559445147237815 := by
  unfold tailWord_5601248
  simp only [CollatzResearch.WordTrace]
  refine ⟨102147149005821293921670199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136196198674428391895560265 102147149005821293921670199)
  ·
    refine ⟨153220723508731940882505299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102147149005821293921670199 153220723508731940882505299)
    ·
      refine ⟨229831085263097911323757949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153220723508731940882505299 229831085263097911323757949)
      ·
        refine ⟨86186656973661716746409231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229831085263097911323757949 86186656973661716746409231)
        ·
          refine ⟨129279985460492575119613847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86186656973661716746409231 129279985460492575119613847)
          ·
            refine ⟨193919978190738862679420771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129279985460492575119613847 193919978190738862679420771)
            ·
              refine ⟨290879967286108294019131157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193919978190738862679420771 290879967286108294019131157)
              ·
                refine ⟨13634998466536326282146773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 290879967286108294019131157 13634998466536326282146773)
                ·
                  refine ⟨319570276559445147237815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13634998466536326282146773 319570276559445147237815)
                  ·
                    rfl

theorem cell23_5601248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 7].length) (baseStart_5601248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601248 prefixEnd_5601248 := by exact prefixLift 5601248
  have htrace : WordTrace (prefixWord ++ tailWord_5601248) baseStart_5601248 baseEnd_5601248 := by
    simpa [prefixWord, tailWord_5601248, baseEnd_5601248] using wordTrace_append hprefix tailTrace_5601248
  have hstable : (prefixWord ++ tailWord_5601248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601248).length < 2 ^ (prefixWord ++ tailWord_5601248).sum := by decide
  have hdescent : baseEnd_5601248 < baseStart_5601248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601315 : List Nat := [1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 4]
def baseStart_5601315 : Nat := 118140960795 + 5601315 * 2 ^ 59
def prefixEnd_5601315 : Nat := 4983230072969 + 3 ^ 40 * 5601315 * 2
def baseEnd_5601315 : Nat := 2876166892238857563002527

theorem tailTrace_5601315 : CollatzResearch.WordTrace tailWord_5601315 prefixEnd_5601315 2876166892238857563002527 := by
  unfold tailWord_5601315
  simp only [CollatzResearch.WordTrace]
  refine ⟨204296741702399858286029399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136197827801599905524019599 204296741702399858286029399)
  ·
    refine ⟨306445112553599787429044099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204296741702399858286029399 306445112553599787429044099)
    ·
      refine ⟨459667668830399681143566149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306445112553599787429044099 459667668830399681143566149)
      ·
        refine ⟨86187687905699940214418653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 459667668830399681143566149 86187687905699940214418653)
        ·
          refine ⟨32320382964637477580406995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86187687905699940214418653 32320382964637477580406995)
          ·
            refine ⟨48480574446956216370610493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32320382964637477580406995 48480574446956216370610493)
            ·
              refine ⟨18180215417608581138978935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48480574446956216370610493 18180215417608581138978935)
              ·
                refine ⟨27270323126412871708468403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18180215417608581138978935 27270323126412871708468403)
                ·
                  refine ⟨40905484689619307562702605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27270323126412871708468403 40905484689619307562702605)
                  ·
                    refine ⟨15339556758607240336013477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40905484689619307562702605 15339556758607240336013477)
                    ·
                      refine ⟨2876166892238857563002527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15339556758607240336013477 2876166892238857563002527)
                      ·
                        rfl

theorem cell23_5601315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_5601315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601315 prefixEnd_5601315 := by exact prefixLift 5601315
  have htrace : WordTrace (prefixWord ++ tailWord_5601315) baseStart_5601315 baseEnd_5601315 := by
    simpa [prefixWord, tailWord_5601315, baseEnd_5601315] using wordTrace_append hprefix tailTrace_5601315
  have hstable : (prefixWord ++ tailWord_5601315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601315).length < 2 ^ (prefixWord ++ tailWord_5601315).sum := by decide
  have hdescent : baseEnd_5601315 < baseStart_5601315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601376 : List Nat := [2, 1, 1, 3, 2, 5, 1, 3, 1, 4]
def baseStart_5601376 : Nat := 118140960795 + 5601376 * 2 ^ 59
def prefixEnd_5601376 : Nat := 4983230072969 + 3 ^ 40 * 5601376 * 2
def baseEnd_5601376 : Nat := 958732738186260608113249

theorem tailTrace_5601376 : CollatzResearch.WordTrace tailWord_5601376 prefixEnd_5601376 958732738186260608113249 := by
  unfold tailWord_5601376
  simp only [CollatzResearch.WordTrace]
  refine ⟨102149483277589432851999991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136199311036785910469333321 102149483277589432851999991)
  ·
    refine ⟨153224224916384149277999987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102149483277589432851999991 153224224916384149277999987)
    ·
      refine ⟨229836337374576223916999981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153224224916384149277999987 229836337374576223916999981)
      ·
        refine ⟨86188626515466083968874993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229836337374576223916999981 86188626515466083968874993)
        ·
          refine ⟨64641469886599562976656245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86188626515466083968874993 64641469886599562976656245)
          ·
            refine ⟨6060137801868709029061523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64641469886599562976656245 6060137801868709029061523)
            ·
              refine ⟨9090206702803063543592285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6060137801868709029061523 9090206702803063543592285)
              ·
                refine ⟨3408827513551148828847107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9090206702803063543592285 3408827513551148828847107)
                ·
                  refine ⟨5113241270326723243270661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3408827513551148828847107 5113241270326723243270661)
                  ·
                    refine ⟨958732738186260608113249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5113241270326723243270661 958732738186260608113249)
                    ·
                      rfl

theorem cell23_5601376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 3, 1, 4].length) (baseStart_5601376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601376 prefixEnd_5601376 := by exact prefixLift 5601376
  have htrace : WordTrace (prefixWord ++ tailWord_5601376) baseStart_5601376 baseEnd_5601376 := by
    simpa [prefixWord, tailWord_5601376, baseEnd_5601376] using wordTrace_append hprefix tailTrace_5601376
  have hstable : (prefixWord ++ tailWord_5601376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601376).length < 2 ^ (prefixWord ++ tailWord_5601376).sum := by decide
  have hdescent : baseEnd_5601376 < baseStart_5601376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601399 : List Nat := [1, 1, 3, 1, 1, 5, 3, 1, 3, 1, 3]
def baseStart_5601399 : Nat := 118140960795 + 5601399 * 2 ^ 59
def prefixEnd_5601399 : Nat := 4983230072969 + 3 ^ 40 * 5601399 * 2
def baseEnd_5601399 : Nat := 2876210024613835234352141

theorem tailTrace_5601399 : CollatzResearch.WordTrace tailWord_5601399 prefixEnd_5601399 2876210024613835234352141 := by
  unfold tailWord_5601399
  simp only [CollatzResearch.WordTrace]
  refine ⟨204299805434095540632087251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136199870289397027088058167 204299805434095540632087251)
  ·
    refine ⟨306449708151143310948130877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204299805434095540632087251 306449708151143310948130877)
    ·
      refine ⟨114918640556678741605549079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306449708151143310948130877 114918640556678741605549079)
      ·
        refine ⟨172377960835018112408323619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114918640556678741605549079 172377960835018112408323619)
        ·
          refine ⟨258566941252527168612485429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172377960835018112408323619 258566941252527168612485429)
          ·
            refine ⟨24240650742424422057420509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 258566941252527168612485429 24240650742424422057420509)
            ·
              refine ⟨9090244028409158271532691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24240650742424422057420509 9090244028409158271532691)
              ·
                refine ⟨13635366042613737407299037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9090244028409158271532691 13635366042613737407299037)
                ·
                  refine ⟨5113262265980151527737139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13635366042613737407299037 5113262265980151527737139)
                  ·
                    refine ⟨7669893398970227291605709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5113262265980151527737139 7669893398970227291605709)
                    ·
                      refine ⟨2876210024613835234352141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7669893398970227291605709 2876210024613835234352141)
                      ·
                        rfl

theorem cell23_5601399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 3, 1, 3].length) (baseStart_5601399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601399 prefixEnd_5601399 := by exact prefixLift 5601399
  have htrace : WordTrace (prefixWord ++ tailWord_5601399) baseStart_5601399 baseEnd_5601399 := by
    simpa [prefixWord, tailWord_5601399, baseEnd_5601399] using wordTrace_append hprefix tailTrace_5601399
  have hstable : (prefixWord ++ tailWord_5601399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601399).length < 2 ^ (prefixWord ++ tailWord_5601399).sum := by decide
  have hdescent : baseEnd_5601399 < baseStart_5601399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601426 : List Nat := [3, 2, 3, 1, 1, 1, 4, 1, 2, 3, 2]
def baseStart_5601426 : Nat := 118140960795 + 5601426 * 2 ^ 59
def prefixEnd_5601426 : Nat := 4983230072969 + 3 ^ 40 * 5601426 * 2
def baseEnd_5601426 : Nat := 2876223888591506628714517

theorem tailTrace_5601426 : CollatzResearch.WordTrace tailWord_5601426 prefixEnd_5601426 2876223888591506628714517 := by
  unfold tailWord_5601426
  simp only [CollatzResearch.WordTrace]
  refine ⟨51075197551249431060830033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136200526803331816162213421 51075197551249431060830033)
  ·
    refine ⟨38306398163437073295622525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51075197551249431060830033 38306398163437073295622525)
    ·
      refine ⟨14364899311288902485858447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38306398163437073295622525 14364899311288902485858447)
      ·
        refine ⟨21547348966933353728787671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14364899311288902485858447 21547348966933353728787671)
        ·
          refine ⟨32321023450400030593181507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21547348966933353728787671 32321023450400030593181507)
          ·
            refine ⟨48481535175600045889772261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32321023450400030593181507 48481535175600045889772261)
            ·
              refine ⟨9090287845425008604332299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48481535175600045889772261 9090287845425008604332299)
              ·
                refine ⟨13635431768137512906498449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9090287845425008604332299 13635431768137512906498449)
                ·
                  refine ⟨10226573826103134679873837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13635431768137512906498449 10226573826103134679873837)
                  ·
                    refine ⟨3834965184788675504952689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10226573826103134679873837 3834965184788675504952689)
                    ·
                      refine ⟨2876223888591506628714517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3834965184788675504952689 2876223888591506628714517)
                      ·
                        rfl

theorem cell23_5601426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_5601426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601426 prefixEnd_5601426 := by exact prefixLift 5601426
  have htrace : WordTrace (prefixWord ++ tailWord_5601426) baseStart_5601426 baseEnd_5601426 := by
    simpa [prefixWord, tailWord_5601426, baseEnd_5601426] using wordTrace_append hprefix tailTrace_5601426
  have hstable : (prefixWord ++ tailWord_5601426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601426).length < 2 ^ (prefixWord ++ tailWord_5601426).sum := by decide
  have hdescent : baseEnd_5601426 < baseStart_5601426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601450 : List Nat := [3, 1, 5, 1, 2, 1, 1, 4, 1, 1, 3]
def baseStart_5601450 : Nat := 118140960795 + 5601450 * 2 ^ 59
def prefixEnd_5601450 : Nat := 4983230072969 + 3 ^ 40 * 5601450 * 2
def baseEnd_5601450 : Nat := 2876236212127214534814407

theorem tailTrace_5601450 : CollatzResearch.WordTrace tailWord_5601450 prefixEnd_5601450 2876236212127214534814407 := by
  unfold tailWord_5601450
  simp only [CollatzResearch.WordTrace]
  refine ⟨51075416389227694085548451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136201110371273850894795869 51075416389227694085548451)
  ·
    refine ⟨76613124583841541128322677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51075416389227694085548451 76613124583841541128322677)
    ·
      refine ⟨7182480429735144480780251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76613124583841541128322677 7182480429735144480780251)
      ·
        refine ⟨10773720644602716721170377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7182480429735144480780251 10773720644602716721170377)
        ·
          refine ⟨8080290483452037540877783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10773720644602716721170377 8080290483452037540877783)
          ·
            refine ⟨12120435725178056311316675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8080290483452037540877783 12120435725178056311316675)
            ·
              refine ⟨18180653587767084466975013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12120435725178056311316675 18180653587767084466975013)
              ·
                refine ⟨3408872547706328337557815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18180653587767084466975013 3408872547706328337557815)
                ·
                  refine ⟨5113308821559492506336723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3408872547706328337557815 5113308821559492506336723)
                  ·
                    refine ⟨7669963232339238759505085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5113308821559492506336723 7669963232339238759505085)
                    ·
                      refine ⟨2876236212127214534814407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7669963232339238759505085 2876236212127214534814407)
                      ·
                        rfl

theorem cell23_5601450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_5601450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601450 prefixEnd_5601450 := by exact prefixLift 5601450
  have htrace : WordTrace (prefixWord ++ tailWord_5601450) baseStart_5601450 baseEnd_5601450 := by
    simpa [prefixWord, tailWord_5601450, baseEnd_5601450] using wordTrace_append hprefix tailTrace_5601450
  have hstable : (prefixWord ++ tailWord_5601450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601450).length < 2 ^ (prefixWord ++ tailWord_5601450).sum := by decide
  have hdescent : baseEnd_5601450 < baseStart_5601450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601490 : List Nat := [3, 2, 2, 2, 1, 3, 2, 3, 1, 2, 2]
def baseStart_5601490 : Nat := 118140960795 + 5601490 * 2 ^ 59
def prefixEnd_5601490 : Nat := 4983230072969 + 3 ^ 40 * 5601490 * 2
def baseEnd_5601490 : Nat := 2876256751353394378314223

theorem tailTrace_5601490 : CollatzResearch.WordTrace tailWord_5601490 prefixEnd_5601490 2876256751353394378314223 := by
  unfold tailWord_5601490
  simp only [CollatzResearch.WordTrace]
  refine ⟨51075781119191465793412481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136202082984510575449099949 51075781119191465793412481)
  ·
    refine ⟨38306835839393599345059361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51075781119191465793412481 38306835839393599345059361)
    ·
      refine ⟨28730126879545199508794521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38306835839393599345059361 28730126879545199508794521)
      ·
        refine ⟨21547595159658899631595891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28730126879545199508794521 21547595159658899631595891)
        ·
          refine ⟨32321392739488349447393837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21547595159658899631595891 32321392739488349447393837)
          ·
            refine ⟨12120522277308131042772689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32321392739488349447393837 12120522277308131042772689)
            ·
              refine ⟨9090391707981098282079517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12120522277308131042772689 9090391707981098282079517)
              ·
                refine ⟨3408896890492911855779819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9090391707981098282079517 3408896890492911855779819)
                ·
                  refine ⟨5113345335739367783669729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3408896890492911855779819 5113345335739367783669729)
                  ·
                    refine ⟨3835009001804525837752297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5113345335739367783669729 3835009001804525837752297)
                    ·
                      refine ⟨2876256751353394378314223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3835009001804525837752297 2876256751353394378314223)
                      ·
                        rfl

theorem cell23_5601490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_5601490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601490 prefixEnd_5601490 := by exact prefixLift 5601490
  have htrace : WordTrace (prefixWord ++ tailWord_5601490) baseStart_5601490 baseEnd_5601490 := by
    simpa [prefixWord, tailWord_5601490, baseEnd_5601490] using wordTrace_append hprefix tailTrace_5601490
  have hstable : (prefixWord ++ tailWord_5601490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601490).length < 2 ^ (prefixWord ++ tailWord_5601490).sum := by decide
  have hdescent : baseEnd_5601490 < baseStart_5601490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601500 : List Nat := [2, 2, 5, 2, 1, 2, 1, 2, 2, 4]
def baseStart_5601500 : Nat := 118140960795 + 5601500 * 2 ^ 59
def prefixEnd_5601500 : Nat := 4983230072969 + 3 ^ 40 * 5601500 * 2
def baseEnd_5601500 : Nat := 958753962053313113063059

theorem tailTrace_5601500 : CollatzResearch.WordTrace tailWord_5601500 prefixEnd_5601500 958753962053313113063059 := by
  unfold tailWord_5601500
  simp only [CollatzResearch.WordTrace]
  refine ⟨102151744603364817440756977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136202326137819756587675969 102151744603364817440756977)
  ·
    refine ⟨76613808452523613080567733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102151744603364817440756977 76613808452523613080567733)
    ·
      refine ⟨7182544542424088726303225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76613808452523613080567733 7182544542424088726303225)
      ·
        refine ⟨5386908406818066544727419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7182544542424088726303225 5386908406818066544727419)
        ·
          refine ⟨8080362610227099817091129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5386908406818066544727419 8080362610227099817091129)
          ·
            refine ⟨6060271957670324862818347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8080362610227099817091129 6060271957670324862818347)
            ·
              refine ⟨9090407936505487294227521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6060271957670324862818347 9090407936505487294227521)
              ·
                refine ⟨6817805952379115470670641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9090407936505487294227521 6817805952379115470670641)
                ·
                  refine ⟨5113354464284336603002981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6817805952379115470670641 5113354464284336603002981)
                  ·
                    refine ⟨958753962053313113063059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5113354464284336603002981 958753962053313113063059)
                    ·
                      rfl

theorem cell23_5601500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_5601500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601500 prefixEnd_5601500 := by exact prefixLift 5601500
  have htrace : WordTrace (prefixWord ++ tailWord_5601500) baseStart_5601500 baseEnd_5601500 := by
    simpa [prefixWord, tailWord_5601500, baseEnd_5601500] using wordTrace_append hprefix tailTrace_5601500
  have hstable : (prefixWord ++ tailWord_5601500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601500).length < 2 ^ (prefixWord ++ tailWord_5601500).sum := by decide
  have hdescent : baseEnd_5601500 < baseStart_5601500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601529 : List Nat := [1, 2, 1, 3, 1, 1, 2, 5, 1, 4, 2]
def baseStart_5601529 : Nat := 118140960795 + 5601529 * 2 ^ 59
def prefixEnd_5601529 : Nat := 4983230072969 + 3 ^ 40 * 5601529 * 2
def baseEnd_5601529 : Nat := 2876276777098919725726543

theorem tailTrace_5601529 : CollatzResearch.WordTrace tailWord_5601529 prefixEnd_5601529 2876276777098919725726543 := by
  unfold tailWord_5601529
  simp only [CollatzResearch.WordTrace]
  refine ⟨204304546923624572834319641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136203031282416381889546427 204304546923624572834319641)
  ·
    refine ⟨153228410192718429625739731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204304546923624572834319641 153228410192718429625739731)
    ·
      refine ⟨229842615289077644438609597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153228410192718429625739731 229842615289077644438609597)
      ·
        refine ⟨86190980733404116664478599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229842615289077644438609597 86190980733404116664478599)
        ·
          refine ⟨129286471100106174996717899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86190980733404116664478599 129286471100106174996717899)
          ·
            refine ⟨193929706650159262495076849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129286471100106174996717899 193929706650159262495076849)
            ·
              refine ⟨145447279987619446871307637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193929706650159262495076849 145447279987619446871307637)
              ·
                refine ⟨13635682498839323144185091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145447279987619446871307637 13635682498839323144185091)
                ·
                  refine ⟨20453523748258984716277637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13635682498839323144185091 20453523748258984716277637)
                  ·
                    refine ⟨3835035702798559634302057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20453523748258984716277637 3835035702798559634302057)
                    ·
                      refine ⟨2876276777098919725726543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3835035702798559634302057 2876276777098919725726543)
                      ·
                        rfl

theorem cell23_5601529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 4, 2].length) (baseStart_5601529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601529 prefixEnd_5601529 := by exact prefixLift 5601529
  have htrace : WordTrace (prefixWord ++ tailWord_5601529) baseStart_5601529 baseEnd_5601529 := by
    simpa [prefixWord, tailWord_5601529, baseEnd_5601529] using wordTrace_append hprefix tailTrace_5601529
  have hstable : (prefixWord ++ tailWord_5601529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601529).length < 2 ^ (prefixWord ++ tailWord_5601529).sum := by decide
  have hdescent : baseEnd_5601529 < baseStart_5601529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601546 : List Nat := [3, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2]
def baseStart_5601546 : Nat := 118140960795 + 5601546 * 2 ^ 59
def prefixEnd_5601546 : Nat := 4983230072969 + 3 ^ 40 * 5601546 * 2
def baseEnd_5601546 : Nat := 2876285506270046159213965

theorem tailTrace_5601546 : CollatzResearch.WordTrace tailWord_5601546 prefixEnd_5601546 2876285506270046159213965 := by
  unfold tailWord_5601546
  simp only [CollatzResearch.WordTrace]
  refine ⟨51076291741140746184422123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136203444643041989825125661 51076291741140746184422123)
  ·
    refine ⟨76614437611711119276633185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51076291741140746184422123 76614437611711119276633185)
    ·
      refine ⟨57460828208783339457474889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76614437611711119276633185 57460828208783339457474889)
      ·
        refine ⟨43095621156587504593106167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57460828208783339457474889 43095621156587504593106167)
        ·
          refine ⟨64643431734881256889659251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43095621156587504593106167 64643431734881256889659251)
          ·
            refine ⟨96965147602321885334488877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64643431734881256889659251 96965147602321885334488877)
            ·
              refine ⟨36361930350870707000433329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96965147602321885334488877 36361930350870707000433329)
              ·
                refine ⟨27271447763153030250324997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36361930350870707000433329 27271447763153030250324997)
                ·
                  refine ⟨5113396455591193171935937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27271447763153030250324997 5113396455591193171935937)
                  ·
                    refine ⟨3835047341693394878951953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5113396455591193171935937 3835047341693394878951953)
                    ·
                      refine ⟨2876285506270046159213965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3835047341693394878951953 2876285506270046159213965)
                      ·
                        rfl

theorem cell23_5601546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_5601546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601546 prefixEnd_5601546 := by exact prefixLift 5601546
  have htrace : WordTrace (prefixWord ++ tailWord_5601546) baseStart_5601546 baseEnd_5601546 := by
    simpa [prefixWord, tailWord_5601546, baseEnd_5601546] using wordTrace_append hprefix tailTrace_5601546
  have hstable : (prefixWord ++ tailWord_5601546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601546).length < 2 ^ (prefixWord ++ tailWord_5601546).sum := by decide
  have hdescent : baseEnd_5601546 < baseStart_5601546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601569 : List Nat := [1, 2, 3, 2, 1, 1, 2, 6, 5]
def baseStart_5601569 : Nat := 118140960795 + 5601569 * 2 ^ 59
def prefixEnd_5601569 : Nat := 4983230072969 + 3 ^ 40 * 5601569 * 2
def baseEnd_5601569 : Nat := 319588590702788841025151

theorem tailTrace_5601569 : CollatzResearch.WordTrace tailWord_5601569 prefixEnd_5601569 319588590702788841025151 := by
  unfold tailWord_5601569
  simp only [CollatzResearch.WordTrace]
  refine ⟨204306005843479659665775761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136204003895653106443850507 204306005843479659665775761)
  ·
    refine ⟨153229504382609744749331821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204306005843479659665775761 153229504382609744749331821)
    ·
      refine ⟨57461064143478654280999433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153229504382609744749331821 57461064143478654280999433)
      ·
        refine ⟨43095798107608990710749575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57461064143478654280999433 43095798107608990710749575)
        ·
          refine ⟨64643697161413486066124363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43095798107608990710749575 64643697161413486066124363)
          ·
            refine ⟨96965545742120229099186545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64643697161413486066124363 96965545742120229099186545)
            ·
              refine ⟨72724159306590171824389909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96965545742120229099186545 72724159306590171824389909)
              ·
                refine ⟨3408944967496414304268277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72724159306590171824389909 3408944967496414304268277)
                ·
                  refine ⟨319588590702788841025151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3408944967496414304268277 319588590702788841025151)
                  ·
                    rfl

theorem cell23_5601569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 6, 5].length) (baseStart_5601569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601569 prefixEnd_5601569 := by exact prefixLift 5601569
  have htrace : WordTrace (prefixWord ++ tailWord_5601569) baseStart_5601569 baseEnd_5601569 := by
    simpa [prefixWord, tailWord_5601569, baseEnd_5601569] using wordTrace_append hprefix tailTrace_5601569
  have hstable : (prefixWord ++ tailWord_5601569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601569).length < 2 ^ (prefixWord ++ tailWord_5601569).sum := by decide
  have hdescent : baseEnd_5601569 < baseStart_5601569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601599 : List Nat := [1, 1, 2, 2, 4, 1, 4, 1, 2, 5]
def baseStart_5601599 : Nat := 118140960795 + 5601599 * 2 ^ 59
def prefixEnd_5601599 : Nat := 4983230072969 + 3 ^ 40 * 5601599 * 2
def baseEnd_5601599 : Nat := 958770906914911483950407

theorem tailTrace_5601599 : CollatzResearch.WordTrace tailWord_5601599 prefixEnd_5601599 958770906914911483950407 := by
  unfold tailWord_5601599
  simp only [CollatzResearch.WordTrace]
  refine ⟨204307100033370974789367851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136204733355580649859578567 204307100033370974789367851)
  ·
    refine ⟨306460650050056462184051777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204307100033370974789367851 306460650050056462184051777)
    ·
      refine ⟨229845487537542346638038833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306460650050056462184051777 229845487537542346638038833)
      ·
        refine ⟨172384115653156759978529125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229845487537542346638038833 172384115653156759978529125)
        ·
          refine ⟨32322021684966892495974211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172384115653156759978529125 32322021684966892495974211)
          ·
            refine ⟨48483032527450338743961317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32322021684966892495974211 48483032527450338743961317)
            ·
              refine ⟨9090568598896938514492747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48483032527450338743961317 9090568598896938514492747)
              ·
                refine ⟨13635852898345407771739121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9090568598896938514492747 13635852898345407771739121)
                ·
                  refine ⟨10226889673759055828804341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13635852898345407771739121 10226889673759055828804341)
                  ·
                    refine ⟨958770906914911483950407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10226889673759055828804341 958770906914911483950407)
                    ·
                      rfl

theorem cell23_5601599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 5].length) (baseStart_5601599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601599 prefixEnd_5601599 := by exact prefixLift 5601599
  have htrace : WordTrace (prefixWord ++ tailWord_5601599) baseStart_5601599 baseEnd_5601599 := by
    simpa [prefixWord, tailWord_5601599, baseEnd_5601599] using wordTrace_append hprefix tailTrace_5601599
  have hstable : (prefixWord ++ tailWord_5601599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601599).length < 2 ^ (prefixWord ++ tailWord_5601599).sum := by decide
  have hdescent : baseEnd_5601599 < baseStart_5601599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601636 : List Nat := [2, 3, 1, 1, 3, 1, 3, 1, 2, 4, 2]
def baseStart_5601636 : Nat := 118140960795 + 5601636 * 2 ^ 59
def prefixEnd_5601636 : Nat := 4983230072969 + 3 ^ 40 * 5601636 * 2
def baseEnd_5601636 : Nat := 2876331719528950807088551

theorem tailTrace_5601636 : CollatzResearch.WordTrace tailWord_5601636 prefixEnd_5601636 2876331719528950807088551 := by
  unfold tailWord_5601636
  simp only [CollatzResearch.WordTrace]
  refine ⟨102154224767118465054232381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136205633022824620072309841 102154224767118465054232381)
  ·
    refine ⟨38307834287669424395337143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102154224767118465054232381 38307834287669424395337143)
    ·
      refine ⟨57461751431504136593005715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38307834287669424395337143 57461751431504136593005715)
      ·
        refine ⟨86192627147256204889508573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57461751431504136593005715 86192627147256204889508573)
        ·
          refine ⟨32322235180221076833565715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86192627147256204889508573 32322235180221076833565715)
          ·
            refine ⟨48483352770331615250348573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32322235180221076833565715 48483352770331615250348573)
            ·
              refine ⟨18181257288874355718880715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48483352770331615250348573 18181257288874355718880715)
              ·
                refine ⟨27271885933311533578321073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18181257288874355718880715 27271885933311533578321073)
                ·
                  refine ⟨20453914449983650183740805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27271885933311533578321073 20453914449983650183740805)
                  ·
                    refine ⟨3835108959371934409451401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20453914449983650183740805 3835108959371934409451401)
                    ·
                      refine ⟨2876331719528950807088551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3835108959371934409451401 2876331719528950807088551)
                      ·
                        rfl

theorem cell23_5601636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 2, 4, 2].length) (baseStart_5601636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601636 prefixEnd_5601636 := by exact prefixLift 5601636
  have htrace : WordTrace (prefixWord ++ tailWord_5601636) baseStart_5601636 baseEnd_5601636 := by
    simpa [prefixWord, tailWord_5601636, baseEnd_5601636] using wordTrace_append hprefix tailTrace_5601636
  have hstable : (prefixWord ++ tailWord_5601636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601636).length < 2 ^ (prefixWord ++ tailWord_5601636).sum := by decide
  have hdescent : baseEnd_5601636 < baseStart_5601636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601653 : List Nat := [1, 3, 4, 1, 2, 3, 1, 1, 2, 1, 4]
def baseStart_5601653 : Nat := 118140960795 + 5601653 * 2 ^ 59
def prefixEnd_5601653 : Nat := 4983230072969 + 3 ^ 40 * 5601653 * 2
def baseEnd_5601653 : Nat := 2876340448700077240575973

theorem tailTrace_5601653 : CollatzResearch.WordTrace tailWord_5601653 prefixEnd_5601653 2876340448700077240575973 := by
  unfold tailWord_5601653
  simp only [CollatzResearch.WordTrace]
  refine ⟨204309069575175342011833613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136206046383450228007889075 204309069575175342011833613)
  ·
    refine ⟨76615901090690753254437605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204309069575175342011833613 76615901090690753254437605)
    ·
      refine ⟨14365481454504516235207051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76615901090690753254437605 14365481454504516235207051)
      ·
        refine ⟨21548222181756774352810577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14365481454504516235207051 21548222181756774352810577)
        ·
          refine ⟨16161166636317580764607933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21548222181756774352810577 16161166636317580764607933)
          ·
            refine ⟨6060437488619092786727975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16161166636317580764607933 6060437488619092786727975)
            ·
              refine ⟨9090656232928639180091963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6060437488619092786727975 9090656232928639180091963)
              ·
                refine ⟨13635984349392958770137945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9090656232928639180091963 13635984349392958770137945)
                ·
                  refine ⟨10226988262044719077603459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13635984349392958770137945 10226988262044719077603459)
                  ·
                    refine ⟨15340482393067078616405189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10226988262044719077603459 15340482393067078616405189)
                    ·
                      refine ⟨2876340448700077240575973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15340482393067078616405189 2876340448700077240575973)
                      ·
                        rfl

theorem cell23_5601653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_5601653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601653 prefixEnd_5601653 := by exact prefixLift 5601653
  have htrace : WordTrace (prefixWord ++ tailWord_5601653) baseStart_5601653 baseEnd_5601653 := by
    simpa [prefixWord, tailWord_5601653, baseEnd_5601653] using wordTrace_append hprefix tailTrace_5601653
  have hstable : (prefixWord ++ tailWord_5601653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601653).length < 2 ^ (prefixWord ++ tailWord_5601653).sum := by decide
  have hdescent : baseEnd_5601653 < baseStart_5601653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601676 : List Nat := [2, 2, 1, 2, 1, 6, 1, 2, 6]
def baseStart_5601676 : Nat := 118140960795 + 5601676 * 2 ^ 59
def prefixEnd_5601676 : Nat := 4983230072969 + 3 ^ 40 * 5601676 * 2
def baseEnd_5601676 : Nat := 319594695417236738954263

theorem tailTrace_5601676 : CollatzResearch.WordTrace tailWord_5601676 prefixEnd_5601676 319594695417236738954263 := by
  unfold tailWord_5601676
  simp only [CollatzResearch.WordTrace]
  refine ⟨102154954227046008469960441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136206605636061344626613921 102154954227046008469960441)
  ·
    refine ⟨76616215670284506352470331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102154954227046008469960441 76616215670284506352470331)
    ·
      refine ⟨114924323505426759528705497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76616215670284506352470331 114924323505426759528705497)
      ·
        refine ⟨86193242629070069646529123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114924323505426759528705497 86193242629070069646529123)
        ·
          refine ⟨129289863943605104469793685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86193242629070069646529123 129289863943605104469793685)
          ·
            refine ⟨6060462372356489272021579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 129289863943605104469793685 6060462372356489272021579)
            ·
              refine ⟨9090693558534733908032369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6060462372356489272021579 9090693558534733908032369)
              ·
                refine ⟨6818020168901050431024277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9090693558534733908032369 6818020168901050431024277)
                ·
                  refine ⟨319594695417236738954263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6818020168901050431024277 319594695417236738954263)
                  ·
                    rfl

theorem cell23_5601676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 6].length) (baseStart_5601676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601676 prefixEnd_5601676 := by exact prefixLift 5601676
  have htrace : WordTrace (prefixWord ++ tailWord_5601676) baseStart_5601676 baseEnd_5601676 := by
    simpa [prefixWord, tailWord_5601676, baseEnd_5601676] using wordTrace_append hprefix tailTrace_5601676
  have hstable : (prefixWord ++ tailWord_5601676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601676).length < 2 ^ (prefixWord ++ tailWord_5601676).sum := by decide
  have hdescent : baseEnd_5601676 < baseStart_5601676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601693 : List Nat := [1, 4, 2, 1, 4, 1, 3, 1, 6]
def baseStart_5601693 : Nat := 118140960795 + 5601693 * 2 ^ 59
def prefixEnd_5601693 : Nat := 4983230072969 + 3 ^ 40 * 5601693 * 2
def baseEnd_5601693 : Nat := 319595665325139676008421

theorem tailTrace_5601693 : CollatzResearch.WordTrace tailWord_5601693 prefixEnd_5601693 319595665325139676008421 := by
  unfold tailWord_5601693
  simp only [CollatzResearch.WordTrace]
  refine ⟨204310528495030428843289733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136207018996686952562193155 204310528495030428843289733)
  ·
    refine ⟨38308224092818205408116825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204310528495030428843289733 38308224092818205408116825)
    ·
      refine ⟨28731168069613654056087619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38308224092818205408116825 28731168069613654056087619)
      ·
        refine ⟨43096752104420481084131429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28731168069613654056087619 43096752104420481084131429)
        ·
          refine ⟨8080641019578840203274643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43096752104420481084131429 8080641019578840203274643)
          ·
            refine ⟨12120961529368260304911965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8080641019578840203274643 12120961529368260304911965)
            ·
              refine ⟨4545360573513097614341987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12120961529368260304911965 4545360573513097614341987)
              ·
                refine ⟨6818040860269646421512981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4545360573513097614341987 6818040860269646421512981)
                ·
                  refine ⟨319595665325139676008421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6818040860269646421512981 319595665325139676008421)
                  ·
                    rfl

theorem cell23_5601693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 6].length) (baseStart_5601693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601693 prefixEnd_5601693 := by exact prefixLift 5601693
  have htrace : WordTrace (prefixWord ++ tailWord_5601693) baseStart_5601693 baseEnd_5601693 := by
    simpa [prefixWord, tailWord_5601693, baseEnd_5601693] using wordTrace_append hprefix tailTrace_5601693
  have hstable : (prefixWord ++ tailWord_5601693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601693).length < 2 ^ (prefixWord ++ tailWord_5601693).sum := by decide
  have hdescent : baseEnd_5601693 < baseStart_5601693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601696 : List Nat := [2, 1, 1, 4, 1, 3, 1, 2, 1, 5, 2]
def baseStart_5601696 : Nat := 118140960795 + 5601696 * 2 ^ 59
def prefixEnd_5601696 : Nat := 4983230072969 + 3 ^ 40 * 5601696 * 2
def baseEnd_5601696 : Nat := 2876362528368220572338275

theorem tailTrace_5601696 : CollatzResearch.WordTrace tailWord_5601696 prefixEnd_5601696 2876362528368220572338275 := by
  unfold tailWord_5601696
  simp only [CollatzResearch.WordTrace]
  refine ⟨102155318957009780177824471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136207091942679706903765961 102155318957009780177824471)
  ·
    refine ⟨153232978435514670266736707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102155318957009780177824471 153232978435514670266736707)
    ·
      refine ⟨229849467653272005400105061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153232978435514670266736707 229849467653272005400105061)
      ·
        refine ⟨43096775184988501012519699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 229849467653272005400105061 43096775184988501012519699)
        ·
          refine ⟨64645162777482751518779549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43096775184988501012519699 64645162777482751518779549)
          ·
            refine ⟨24241936041556031819542331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64645162777482751518779549 24241936041556031819542331)
            ·
              refine ⟨36362904062334047729313497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24241936041556031819542331 36362904062334047729313497)
              ·
                refine ⟨27272178046750535796985123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36362904062334047729313497 27272178046750535796985123)
                ·
                  refine ⟨40908267070125803695477685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27272178046750535796985123 40908267070125803695477685)
                  ·
                    refine ⟨3835150037824294096451033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40908267070125803695477685 3835150037824294096451033)
                    ·
                      refine ⟨2876362528368220572338275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3835150037824294096451033 2876362528368220572338275)
                      ·
                        rfl

theorem cell23_5601696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_5601696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601696 prefixEnd_5601696 := by exact prefixLift 5601696
  have htrace : WordTrace (prefixWord ++ tailWord_5601696) baseStart_5601696 baseEnd_5601696 := by
    simpa [prefixWord, tailWord_5601696, baseEnd_5601696] using wordTrace_append hprefix tailTrace_5601696
  have hstable : (prefixWord ++ tailWord_5601696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601696).length < 2 ^ (prefixWord ++ tailWord_5601696).sum := by decide
  have hdescent : baseEnd_5601696 < baseStart_5601696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601703 : List Nat := [1, 1, 6, 1, 1, 2, 2, 2, 3, 1, 3]
def baseStart_5601703 : Nat := 118140960795 + 5601703 * 2 ^ 59
def prefixEnd_5601703 : Nat := 4983230072969 + 3 ^ 40 * 5601703 * 2
def baseEnd_5601703 : Nat := 2876366122732802044950743

theorem tailTrace_5601703 : CollatzResearch.WordTrace tailWord_5601703 prefixEnd_5601703 2876366122732802044950743 := by
  unfold tailWord_5601703
  simp only [CollatzResearch.WordTrace]
  refine ⟨204310893224994200551153763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136207262149996133700769175 204310893224994200551153763)
  ·
    refine ⟨306466339837491300826730645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204310893224994200551153763 306466339837491300826730645)
    ·
      refine ⟨14365609679882404726252999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 306466339837491300826730645 14365609679882404726252999)
      ·
        refine ⟨21548414519823607089379499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14365609679882404726252999 21548414519823607089379499)
        ·
          refine ⟨32322621779735410634069249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21548414519823607089379499 32322621779735410634069249)
          ·
            refine ⟨24241966334801557975551937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32322621779735410634069249 24241966334801557975551937)
            ·
              refine ⟨18181474751101168481663953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24241966334801557975551937 18181474751101168481663953)
              ·
                refine ⟨13636106063325876361247965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18181474751101168481663953 13636106063325876361247965)
                ·
                  refine ⟨5113539773747203635467987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13636106063325876361247965 5113539773747203635467987)
                  ·
                    refine ⟨7670309660620805453201981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5113539773747203635467987 7670309660620805453201981)
                    ·
                      refine ⟨2876366122732802044950743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7670309660620805453201981 2876366122732802044950743)
                      ·
                        rfl

theorem cell23_5601703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_5601703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601703 prefixEnd_5601703 := by exact prefixLift 5601703
  have htrace : WordTrace (prefixWord ++ tailWord_5601703) baseStart_5601703 baseEnd_5601703 := by
    simpa [prefixWord, tailWord_5601703, baseEnd_5601703] using wordTrace_append hprefix tailTrace_5601703
  have hstable : (prefixWord ++ tailWord_5601703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601703).length < 2 ^ (prefixWord ++ tailWord_5601703).sum := by decide
  have hdescent : baseEnd_5601703 < baseStart_5601703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601736 : List Nat := [2, 1, 3, 1, 3, 2, 2, 1, 4, 4]
def baseStart_5601736 : Nat := 118140960795 + 5601736 * 2 ^ 59
def prefixEnd_5601736 : Nat := 4983230072969 + 3 ^ 40 * 5601736 * 2
def baseEnd_5601736 : Nat := 958794355864800138612697

theorem tailTrace_5601736 : CollatzResearch.WordTrace tailWord_5601736 prefixEnd_5601736 958794355864800138612697 := by
  unfold tailWord_5601736
  simp only [CollatzResearch.WordTrace]
  refine ⟨102156048416937323593552531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136208064555916431458070041 102156048416937323593552531)
  ·
    refine ⟨153234072625405985390328797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102156048416937323593552531 153234072625405985390328797)
    ·
      refine ⟨57462777234527244521373299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153234072625405985390328797 57462777234527244521373299)
      ·
        refine ⟨86194165851790866782059949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57462777234527244521373299 86194165851790866782059949)
        ·
          refine ⟨32322812194421575043272481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86194165851790866782059949 32322812194421575043272481)
          ·
            refine ⟨24242109145816181282454361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32322812194421575043272481 24242109145816181282454361)
            ·
              refine ⟨18181581859362135961840771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24242109145816181282454361 18181581859362135961840771)
              ·
                refine ⟨27272372789043203942761157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18181581859362135961840771 27272372789043203942761157)
                ·
                  refine ⟨5113569897945600739267717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27272372789043203942761157 5113569897945600739267717)
                  ·
                    refine ⟨958794355864800138612697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5113569897945600739267717 958794355864800138612697)
                    ·
                      rfl

theorem cell23_5601736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_5601736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601736 prefixEnd_5601736 := by exact prefixLift 5601736
  have htrace : WordTrace (prefixWord ++ tailWord_5601736) baseStart_5601736 baseEnd_5601736 := by
    simpa [prefixWord, tailWord_5601736, baseEnd_5601736] using wordTrace_append hprefix tailTrace_5601736
  have hstable : (prefixWord ++ tailWord_5601736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601736).length < 2 ^ (prefixWord ++ tailWord_5601736).sum := by decide
  have hdescent : baseEnd_5601736 < baseStart_5601736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601749 : List Nat := [1, 3, 2, 3, 1, 2, 1, 10]
def baseStart_5601749 : Nat := 118140960795 + 5601749 * 2 ^ 59
def prefixEnd_5601749 : Nat := 4983230072969 + 3 ^ 40 * 5601749 * 2
def baseEnd_5601749 : Nat := 106532953438626254258353

theorem tailTrace_5601749 : CollatzResearch.WordTrace tailWord_5601749 prefixEnd_5601749 106532953438626254258353 := by
  unfold tailWord_5601749
  simp only [CollatzResearch.WordTrace]
  refine ⟨204312570982827550407328301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136208380655218366938218867 204312570982827550407328301)
  ·
    refine ⟨76617214118560331402748113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204312570982827550407328301 76617214118560331402748113)
    ·
      refine ⟨57462910588920248552061085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76617214118560331402748113 57462910588920248552061085)
      ·
        refine ⟨21548591470845093207022907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57462910588920248552061085 21548591470845093207022907)
        ·
          refine ⟨32322887206267639810534361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21548591470845093207022907 32322887206267639810534361)
          ·
            refine ⟨24242165404700729857900771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32322887206267639810534361 24242165404700729857900771)
            ·
              refine ⟨36363248107051094786851157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24242165404700729857900771 36363248107051094786851157)
              ·
                refine ⟨106532953438626254258353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36363248107051094786851157 106532953438626254258353)
                ·
                  rfl

theorem cell23_5601749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 10].length) (baseStart_5601749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601749 prefixEnd_5601749 := by exact prefixLift 5601749
  have htrace : WordTrace (prefixWord ++ tailWord_5601749) baseStart_5601749 baseEnd_5601749 := by
    simpa [prefixWord, tailWord_5601749, baseEnd_5601749] using wordTrace_append hprefix tailTrace_5601749
  have hstable : (prefixWord ++ tailWord_5601749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601749).length < 2 ^ (prefixWord ++ tailWord_5601749).sum := by decide
  have hdescent : baseEnd_5601749 < baseStart_5601749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601763 : List Nat := [1, 1, 1, 6, 3, 1, 1, 1, 3, 2, 3]
def baseStart_5601763 : Nat := 118140960795 + 5601763 * 2 ^ 59
def prefixEnd_5601763 : Nat := 4983230072969 + 3 ^ 40 * 5601763 * 2
def baseEnd_5601763 : Nat := 2876396931572071810200467

theorem tailTrace_5601763 : CollatzResearch.WordTrace tailWord_5601763 prefixEnd_5601763 2876396931572071810200467 := by
  unfold tailWord_5601763
  simp only [CollatzResearch.WordTrace]
  refine ⟨204313081604776830798337943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136208721069851220532225295 204313081604776830798337943)
  ·
    refine ⟨306469622407165246197506915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204313081604776830798337943 306469622407165246197506915)
    ·
      refine ⟨459704433610747869296260373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306469622407165246197506915 459704433610747869296260373)
      ·
        refine ⟨21548645325503806373262205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 459704433610747869296260373 21548645325503806373262205)
        ·
          refine ⟨8080741997063927389973327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21548645325503806373262205 8080741997063927389973327)
          ·
            refine ⟨12121112995595891084959991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8080741997063927389973327 12121112995595891084959991)
            ·
              refine ⟨18181669493393836627439987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12121112995595891084959991 18181669493393836627439987)
              ·
                refine ⟨27272504240090754941159981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18181669493393836627439987 27272504240090754941159981)
                ·
                  refine ⟨10227189090034033102934993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27272504240090754941159981 10227189090034033102934993)
                  ·
                    refine ⟨7670391817525524827201245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10227189090034033102934993 7670391817525524827201245)
                    ·
                      refine ⟨2876396931572071810200467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7670391817525524827201245 2876396931572071810200467)
                      ·
                        rfl

theorem cell23_5601763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_5601763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601763 prefixEnd_5601763 := by exact prefixLift 5601763
  have htrace : WordTrace (prefixWord ++ tailWord_5601763) baseStart_5601763 baseEnd_5601763 := by
    simpa [prefixWord, tailWord_5601763, baseEnd_5601763] using wordTrace_append hprefix tailTrace_5601763
  have hstable : (prefixWord ++ tailWord_5601763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601763).length < 2 ^ (prefixWord ++ tailWord_5601763).sum := by decide
  have hdescent : baseEnd_5601763 < baseStart_5601763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601773 : List Nat := [1, 5, 1, 3, 1, 2, 1, 2, 1, 2, 4]
def baseStart_5601773 : Nat := 118140960795 + 5601773 * 2 ^ 59
def prefixEnd_5601773 : Nat := 4983230072969 + 3 ^ 40 * 5601773 * 2
def baseEnd_5601773 : Nat := 2876402066378616771075421

theorem tailTrace_5601773 : CollatzResearch.WordTrace tailWord_5601773 prefixEnd_5601773 2876402066378616771075421 := by
  unfold tailWord_5601773
  simp only [CollatzResearch.WordTrace]
  refine ⟨204313446334740602506201973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136208964223160401670801315 204313446334740602506201973)
  ·
    refine ⟨19154385593881931484956435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 204313446334740602506201973 19154385593881931484956435)
    ·
      refine ⟨28731578390822897227434653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19154385593881931484956435 28731578390822897227434653)
      ·
        refine ⟨10774341896558586460287995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28731578390822897227434653 10774341896558586460287995)
        ·
          refine ⟨16161512844837879690431993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10774341896558586460287995 16161512844837879690431993)
          ·
            refine ⟨12121134633628409767823995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16161512844837879690431993 12121134633628409767823995)
            ·
              refine ⟨18181701950442614651735993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12121134633628409767823995 18181701950442614651735993)
              ·
                refine ⟨13636276462831960988801995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18181701950442614651735993 13636276462831960988801995)
                ·
                  refine ⟨20454414694247941483202993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13636276462831960988801995 20454414694247941483202993)
                  ·
                    refine ⟨15340811020685956112402245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20454414694247941483202993 15340811020685956112402245)
                    ·
                      refine ⟨2876402066378616771075421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15340811020685956112402245 2876402066378616771075421)
                      ·
                        rfl

theorem cell23_5601773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_5601773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601773 prefixEnd_5601773 := by exact prefixLift 5601773
  have htrace : WordTrace (prefixWord ++ tailWord_5601773) baseStart_5601773 baseEnd_5601773 := by
    simpa [prefixWord, tailWord_5601773, baseEnd_5601773] using wordTrace_append hprefix tailTrace_5601773
  have hstable : (prefixWord ++ tailWord_5601773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601773).length < 2 ^ (prefixWord ++ tailWord_5601773).sum := by decide
  have hdescent : baseEnd_5601773 < baseStart_5601773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601776 : List Nat := [2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 3]
def baseStart_5601776 : Nat := 118140960795 + 5601776 * 2 ^ 59
def prefixEnd_5601776 : Nat := 4983230072969 + 3 ^ 40 * 5601776 * 2
def baseEnd_5601776 : Nat := 2876403606820580259337907

theorem tailTrace_5601776 : CollatzResearch.WordTrace tailWord_5601776 prefixEnd_5601776 2876403606820580259337907 := by
  unfold tailWord_5601776
  simp only [CollatzResearch.WordTrace]
  refine ⟨102156777876864867009280591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136209037169153156012374121 102156777876864867009280591)
  ·
    refine ⟨153235166815297300513920887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102156777876864867009280591 153235166815297300513920887)
    ·
      refine ⟨229852750222945950770881331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153235166815297300513920887 229852750222945950770881331)
      ·
        refine ⟨344779125334418926156321997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229852750222945950770881331 344779125334418926156321997)
        ·
          refine ⟨129292172000407097308620749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 344779125334418926156321997 129292172000407097308620749)
          ·
            refine ⟨48484564500152661490732781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129292172000407097308620749 48484564500152661490732781)
            ·
              refine ⟨18181711687557248059024793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48484564500152661490732781 18181711687557248059024793)
              ·
                refine ⟨13636283765667936044268595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18181711687557248059024793 13636283765667936044268595)
                ·
                  refine ⟨20454425648501904066402893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13636283765667936044268595 20454425648501904066402893)
                  ·
                    refine ⟨7670409618188214024901085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20454425648501904066402893 7670409618188214024901085)
                    ·
                      refine ⟨2876403606820580259337907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7670409618188214024901085 2876403606820580259337907)
                      ·
                        rfl

theorem cell23_5601776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 3].length) (baseStart_5601776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601776 prefixEnd_5601776 := by exact prefixLift 5601776
  have htrace : WordTrace (prefixWord ++ tailWord_5601776) baseStart_5601776 baseEnd_5601776 := by
    simpa [prefixWord, tailWord_5601776, baseEnd_5601776] using wordTrace_append hprefix tailTrace_5601776
  have hstable : (prefixWord ++ tailWord_5601776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601776).length < 2 ^ (prefixWord ++ tailWord_5601776).sum := by decide
  have hdescent : baseEnd_5601776 < baseStart_5601776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601796 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 2, 7]
def baseStart_5601796 : Nat := 118140960795 + 5601796 * 2 ^ 59
def prefixEnd_5601796 : Nat := 4983230072969 + 3 ^ 40 * 5601796 * 2
def baseEnd_5601796 : Nat := 958804625477890060362605

theorem tailTrace_5601796 : CollatzResearch.WordTrace tailWord_5601796 prefixEnd_5601796 958804625477890060362605 := by
  unfold tailWord_5601796
  simp only [CollatzResearch.WordTrace]
  refine ⟨102157142606828638717144621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136209523475771518289526161 102157142606828638717144621)
  ·
    refine ⟨38308928477560739518929233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102157142606828638717144621 38308928477560739518929233)
    ·
      refine ⟨28731696358170554639196925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38308928477560739518929233 28731696358170554639196925)
      ·
        refine ⟨10774386134313957989698847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28731696358170554639196925 10774386134313957989698847)
        ·
          refine ⟨16161579201470936984548271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10774386134313957989698847 16161579201470936984548271)
          ·
            refine ⟨24242368802206405476822407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16161579201470936984548271 24242368802206405476822407)
            ·
              refine ⟨36363553203309608215233611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24242368802206405476822407 36363553203309608215233611)
              ·
                refine ⟨54545329804964412322850417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36363553203309608215233611 54545329804964412322850417)
                ·
                  refine ⟨40908997353723309242137813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54545329804964412322850417 40908997353723309242137813)
                  ·
                    refine ⟨958804625477890060362605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40908997353723309242137813 958804625477890060362605)
                    ·
                      rfl

theorem cell23_5601796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_5601796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601796 prefixEnd_5601796 := by exact prefixLift 5601796
  have htrace : WordTrace (prefixWord ++ tailWord_5601796) baseStart_5601796 baseEnd_5601796 := by
    simpa [prefixWord, tailWord_5601796, baseEnd_5601796] using wordTrace_append hprefix tailTrace_5601796
  have hstable : (prefixWord ++ tailWord_5601796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601796).length < 2 ^ (prefixWord ++ tailWord_5601796).sum := by decide
  have hdescent : baseEnd_5601796 < baseStart_5601796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601803 : List Nat := [1, 1, 1, 1, 7, 1, 1, 2, 3, 3, 2]
def baseStart_5601803 : Nat := 118140960795 + 5601803 * 2 ^ 59
def prefixEnd_5601803 : Nat := 4983230072969 + 3 ^ 40 * 5601803 * 2
def baseEnd_5601803 : Nat := 2876417470798251653700283

theorem tailTrace_5601803 : CollatzResearch.WordTrace tailWord_5601803 prefixEnd_5601803 2876417470798251653700283 := by
  unfold tailWord_5601803
  simp only [CollatzResearch.WordTrace]
  refine ⟨204314540524631917629794063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136209693683087945086529375 204314540524631917629794063)
  ·
    refine ⟨306471810786947876444691095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204314540524631917629794063 306471810786947876444691095)
    ·
      refine ⟨459707716180421814667036643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306471810786947876444691095 459707716180421814667036643)
      ·
        refine ⟨689561574270632722000554965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459707716180421814667036643 689561574270632722000554965)
        ·
          refine ⟨16161599396967954421888007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 689561574270632722000554965 16161599396967954421888007)
          ·
            refine ⟨24242399095451931632832011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16161599396967954421888007 24242399095451931632832011)
            ·
              refine ⟨36363598643177897449248017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24242399095451931632832011 36363598643177897449248017)
              ·
                refine ⟨27272698982383423086936013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36363598643177897449248017 27272698982383423086936013)
                ·
                  refine ⟨10227262118393783657601005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27272698982383423086936013 10227262118393783657601005)
                  ·
                    refine ⟨3835223294397668871600377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10227262118393783657601005 3835223294397668871600377)
                    ·
                      refine ⟨2876417470798251653700283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3835223294397668871600377 2876417470798251653700283)
                      ·
                        rfl

theorem cell23_5601803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 3, 2].length) (baseStart_5601803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601803 prefixEnd_5601803 := by exact prefixLift 5601803
  have htrace : WordTrace (prefixWord ++ tailWord_5601803) baseStart_5601803 baseEnd_5601803 := by
    simpa [prefixWord, tailWord_5601803, baseEnd_5601803] using wordTrace_append hprefix tailTrace_5601803
  have hstable : (prefixWord ++ tailWord_5601803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601803).length < 2 ^ (prefixWord ++ tailWord_5601803).sum := by decide
  have hdescent : baseEnd_5601803 < baseStart_5601803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601831 : List Nat := [1, 1, 7, 2, 2, 1, 2, 1, 1, 2, 3]
def baseStart_5601831 : Nat := 118140960795 + 5601831 * 2 ^ 59
def prefixEnd_5601831 : Nat := 4983230072969 + 3 ^ 40 * 5601831 * 2
def baseEnd_5601831 : Nat := 2876431848256577544150155

theorem tailTrace_5601831 : CollatzResearch.WordTrace tailWord_5601831 prefixEnd_5601831 2876431848256577544150155 := by
  unfold tailWord_5601831
  simp only [CollatzResearch.WordTrace]
  refine ⟨204315561768530478411813347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136210374512353652274542231 204315561768530478411813347)
  ·
    refine ⟨306473342652795717617720021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204315561768530478411813347 306473342652795717617720021)
    ·
      refine ⟨7182968968424899631665313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 306473342652795717617720021 7182968968424899631665313)
      ·
        refine ⟨5387226726318674723748985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7182968968424899631665313 5387226726318674723748985)
        ·
          refine ⟨4040420044739006042811739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5387226726318674723748985 4040420044739006042811739)
          ·
            refine ⟨6060630067108509064217609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4040420044739006042811739 6060630067108509064217609)
            ·
              refine ⟨4545472550331381798163207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6060630067108509064217609 4545472550331381798163207)
              ·
                refine ⟨6818208825497072697244811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4545472550331381798163207 6818208825497072697244811)
                ·
                  refine ⟨10227313238245609045867217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6818208825497072697244811 10227313238245609045867217)
                  ·
                    refine ⟨7670484928684206784400413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10227313238245609045867217 7670484928684206784400413)
                    ·
                      refine ⟨2876431848256577544150155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7670484928684206784400413 2876431848256577544150155)
                      ·
                        rfl

theorem cell23_5601831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_5601831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601831 prefixEnd_5601831 := by exact prefixLift 5601831
  have htrace : WordTrace (prefixWord ++ tailWord_5601831) baseStart_5601831 baseEnd_5601831 := by
    simpa [prefixWord, tailWord_5601831, baseEnd_5601831] using wordTrace_append hprefix tailTrace_5601831
  have hstable : (prefixWord ++ tailWord_5601831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601831).length < 2 ^ (prefixWord ++ tailWord_5601831).sum := by decide
  have hdescent : baseEnd_5601831 < baseStart_5601831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601850 : List Nat := [3, 1, 1, 1, 3, 4, 1, 1, 4, 2, 2]
def baseStart_5601850 : Nat := 118140960795 + 5601850 * 2 ^ 59
def prefixEnd_5601850 : Nat := 4983230072969 + 3 ^ 40 * 5601850 * 2
def baseEnd_5601850 : Nat := 2876441604389012969812567

theorem tailTrace_5601850 : CollatzResearch.WordTrace tailWord_5601850 prefixEnd_5601850 2876441604389012969812567 := by
  unfold tailWord_5601850
  simp only [CollatzResearch.WordTrace]
  refine ⟨51079063688865411164188751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136210836503641096437836669 51079063688865411164188751)
  ·
    refine ⟨76618595533298116746283127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51079063688865411164188751 76618595533298116746283127)
    ·
      refine ⟨114927893299947175119424691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76618595533298116746283127 114927893299947175119424691)
      ·
        refine ⟨172391839949920762679137037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114927893299947175119424691 172391839949920762679137037)
        ·
          refine ⟨64646939981220286004676389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172391839949920762679137037 64646939981220286004676389)
          ·
            refine ⟨12121301246478803625876823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64646939981220286004676389 12121301246478803625876823)
            ·
              refine ⟨18181951869718205438815235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12121301246478803625876823 18181951869718205438815235)
              ·
                refine ⟨27272927804577308158222853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18181951869718205438815235 27272927804577308158222853)
                ·
                  refine ⟨5113673963358245279666785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27272927804577308158222853 5113673963358245279666785)
                  ·
                    refine ⟨3835255472518683959750089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5113673963358245279666785 3835255472518683959750089)
                    ·
                      refine ⟨2876441604389012969812567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3835255472518683959750089 2876441604389012969812567)
                      ·
                        rfl

theorem cell23_5601850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 4, 2, 2].length) (baseStart_5601850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601850 prefixEnd_5601850 := by exact prefixLift 5601850
  have htrace : WordTrace (prefixWord ++ tailWord_5601850) baseStart_5601850 baseEnd_5601850 := by
    simpa [prefixWord, tailWord_5601850, baseEnd_5601850] using wordTrace_append hprefix tailTrace_5601850
  have hstable : (prefixWord ++ tailWord_5601850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601850).length < 2 ^ (prefixWord ++ tailWord_5601850).sum := by decide
  have hdescent : baseEnd_5601850 < baseStart_5601850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601923 : List Nat := [1, 1, 1, 3, 3, 1, 2, 3, 2, 4, 2]
def baseStart_5601923 : Nat := 118140960795 + 5601923 * 2 ^ 59
def prefixEnd_5601923 : Nat := 4983230072969 + 3 ^ 40 * 5601923 * 2
def baseEnd_5601923 : Nat := 2876479088476791184199731

theorem tailTrace_5601923 : CollatzResearch.WordTrace tailWord_5601923 prefixEnd_5601923 2876479088476791184199731 := by
  unfold tailWord_5601923
  simp only [CollatzResearch.WordTrace]
  refine ⟨204318917284197178124162423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136212611522798118749441615 204318917284197178124162423)
  ·
    refine ⟨306478375926295767186243635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204318917284197178124162423 306478375926295767186243635)
    ·
      refine ⟨459717563889443650779365453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306478375926295767186243635 459717563889443650779365453)
      ·
        refine ⟨172394086458541369042262045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 459717563889443650779365453 172394086458541369042262045)
        ·
          refine ⟨64647782421953013390848267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172394086458541369042262045 64647782421953013390848267)
          ·
            refine ⟨96971673632929520086272401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64647782421953013390848267 96971673632929520086272401)
            ·
              refine ⟨72728755224697140064704301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96971673632929520086272401 72728755224697140064704301)
              ·
                refine ⟨27273283209261427524264113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72728755224697140064704301 27273283209261427524264113)
                ·
                  refine ⟨20454962406946070643198085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27273283209261427524264113 20454962406946070643198085)
                  ·
                    refine ⟨3835305451302388245599641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20454962406946070643198085 3835305451302388245599641)
                    ·
                      refine ⟨2876479088476791184199731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3835305451302388245599641 2876479088476791184199731)
                      ·
                        rfl

theorem cell23_5601923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 4, 2].length) (baseStart_5601923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601923 prefixEnd_5601923 := by exact prefixLift 5601923
  have htrace : WordTrace (prefixWord ++ tailWord_5601923) baseStart_5601923 baseEnd_5601923 := by
    simpa [prefixWord, tailWord_5601923, baseEnd_5601923] using wordTrace_append hprefix tailTrace_5601923
  have hstable : (prefixWord ++ tailWord_5601923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601923).length < 2 ^ (prefixWord ++ tailWord_5601923).sum := by decide
  have hdescent : baseEnd_5601923 < baseStart_5601923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601940 : List Nat := [2, 4, 2, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_5601940 : Nat := 118140960795 + 5601940 * 2 ^ 59
def prefixEnd_5601940 : Nat := 4983230072969 + 3 ^ 40 * 5601940 * 2
def baseEnd_5601940 : Nat := 2876487817647917617687153

theorem tailTrace_5601940 : CollatzResearch.WordTrace tailWord_5601940 prefixEnd_5601940 2876487817647917617687153 := by
  unfold tailWord_5601940
  simp only [CollatzResearch.WordTrace]
  refine ⟨102159768662567795013765637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136213024883423726685020849 102159768662567795013765637)
  ·
    refine ⟨19154956624231461565081057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102159768662567795013765637 19154956624231461565081057)
    ·
      refine ⟨14366217468173596173810793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19154956624231461565081057 14366217468173596173810793)
      ·
        refine ⟨10774663101130197130358095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14366217468173596173810793 10774663101130197130358095)
        ·
          refine ⟨16161994651695295695537143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10774663101130197130358095 16161994651695295695537143)
          ·
            refine ⟨24242991977542943543305715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16161994651695295695537143 24242991977542943543305715)
            ·
              refine ⟨36364487966314415314958573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24242991977542943543305715 36364487966314415314958573)
              ·
                refine ⟨13636682987367905743109465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36364487966314415314958573 13636682987367905743109465)
                ·
                  refine ⟨10227512240525929307332099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13636682987367905743109465 10227512240525929307332099)
                  ·
                    refine ⟨15341268360788893960998149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10227512240525929307332099 15341268360788893960998149)
                    ·
                      refine ⟨2876487817647917617687153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15341268360788893960998149 2876487817647917617687153)
                      ·
                        rfl

theorem cell23_5601940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_5601940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601940 prefixEnd_5601940 := by exact prefixLift 5601940
  have htrace : WordTrace (prefixWord ++ tailWord_5601940) baseStart_5601940 baseEnd_5601940 := by
    simpa [prefixWord, tailWord_5601940, baseEnd_5601940] using wordTrace_append hprefix tailTrace_5601940
  have hstable : (prefixWord ++ tailWord_5601940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601940).length < 2 ^ (prefixWord ++ tailWord_5601940).sum := by decide
  have hdescent : baseEnd_5601940 < baseStart_5601940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601967 : List Nat := [1, 1, 2, 1, 2, 5, 4, 2, 1, 4]
def baseStart_5601967 : Nat := 118140960795 + 5601967 * 2 ^ 59
def prefixEnd_5601967 : Nat := 4983230072969 + 3 ^ 40 * 5601967 * 2
def baseEnd_5601967 : Nat := 958833893875196337349843

theorem tailTrace_5601967 : CollatzResearch.WordTrace tailWord_5601967 prefixEnd_5601967 958833893875196337349843 := by
  unfold tailWord_5601967
  simp only [CollatzResearch.WordTrace]
  refine ⟨204320522096037773638764155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136213681397358515759176103 204320522096037773638764155)
  ·
    refine ⟨306480783144056660458146233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204320522096037773638764155 306480783144056660458146233)
    ·
      refine ⟨229860587358042495343609675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306480783144056660458146233 229860587358042495343609675)
      ·
        refine ⟨344790881037063743015414513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229860587358042495343609675 344790881037063743015414513)
        ·
          refine ⟨258593160777797807261560885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344790881037063743015414513 258593160777797807261560885)
          ·
            refine ⟨24243108822918544430771333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 258593160777797807261560885 24243108822918544430771333)
            ·
              refine ⟨4545582904297227080769625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24243108822918544430771333 4545582904297227080769625)
              ·
                refine ⟨3409187178222920310577219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4545582904297227080769625 3409187178222920310577219)
                ·
                  refine ⟨5113780767334380465865829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3409187178222920310577219 5113780767334380465865829)
                  ·
                    refine ⟨958833893875196337349843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5113780767334380465865829 958833893875196337349843)
                    ·
                      rfl

theorem cell23_5601967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 2, 1, 4].length) (baseStart_5601967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601967 prefixEnd_5601967 := by exact prefixLift 5601967
  have htrace : WordTrace (prefixWord ++ tailWord_5601967) baseStart_5601967 baseEnd_5601967 := by
    simpa [prefixWord, tailWord_5601967, baseEnd_5601967] using wordTrace_append hprefix tailTrace_5601967
  have hstable : (prefixWord ++ tailWord_5601967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601967).length < 2 ^ (prefixWord ++ tailWord_5601967).sum := by decide
  have hdescent : baseEnd_5601967 < baseStart_5601967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5601974 : List Nat := [5, 1, 3, 1, 2, 1, 1, 1, 2, 4, 2]
def baseStart_5601974 : Nat := 118140960795 + 5601974 * 2 ^ 59
def prefixEnd_5601974 : Nat := 4983230072969 + 3 ^ 40 * 5601974 * 2
def baseEnd_5601974 : Nat := 2876505275990170484661997

theorem tailTrace_5601974 : CollatzResearch.WordTrace tailWord_5601974 prefixEnd_5601974 2876505275990170484661997 := by
  unfold tailWord_5601974
  simp only [CollatzResearch.WordTrace]
  refine ⟨12770048587938275864641811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136213851604674942556179317 12770048587938275864641811)
  ·
    refine ⟨19155072881907413796962717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12770048587938275864641811 19155072881907413796962717)
    ·
      refine ⟨7183152330715280173861019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19155072881907413796962717 7183152330715280173861019)
      ·
        refine ⟨10774728496072920260791529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7183152330715280173861019 10774728496072920260791529)
        ·
          refine ⟨8081046372054690195593647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10774728496072920260791529 8081046372054690195593647)
          ·
            refine ⟨12121569558082035293390471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8081046372054690195593647 12121569558082035293390471)
            ·
              refine ⟨18182354337123052940085707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12121569558082035293390471 18182354337123052940085707)
              ·
                refine ⟨27273531505684579410128561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18182354337123052940085707 27273531505684579410128561)
                ·
                  refine ⟨20455148629263434557596421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27273531505684579410128561 20455148629263434557596421)
                  ·
                    refine ⟨3835340367986893979549329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20455148629263434557596421 3835340367986893979549329)
                    ·
                      refine ⟨2876505275990170484661997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3835340367986893979549329 2876505275990170484661997)
                      ·
                        rfl

theorem cell23_5601974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_5601974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5601974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5601974 prefixEnd_5601974 := by exact prefixLift 5601974
  have htrace : WordTrace (prefixWord ++ tailWord_5601974) baseStart_5601974 baseEnd_5601974 := by
    simpa [prefixWord, tailWord_5601974, baseEnd_5601974] using wordTrace_append hprefix tailTrace_5601974
  have hstable : (prefixWord ++ tailWord_5601974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5601974).length < 2 ^ (prefixWord ++ tailWord_5601974).sum := by decide
  have hdescent : baseEnd_5601974 < baseStart_5601974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5601974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602007 : List Nat := [1, 1, 3, 2, 1, 4, 1, 5, 1, 1, 3]
def baseStart_5602007 : Nat := 118140960795 + 5602007 * 2 ^ 59
def prefixEnd_5602007 : Nat := 4983230072969 + 3 ^ 40 * 5602007 * 2
def baseEnd_5602007 : Nat := 2876522220851768855549345

theorem tailTrace_5602007 : CollatzResearch.WordTrace tailWord_5602007 prefixEnd_5602007 2876522220851768855549345 := by
  unfold tailWord_5602007
  simp only [CollatzResearch.WordTrace]
  refine ⟨204321981015892860470220275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136214654010595240313480183 204321981015892860470220275)
  ·
    refine ⟨306482971523839290705330413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204321981015892860470220275 306482971523839290705330413)
    ·
      refine ⟨114931114321439734014498905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306482971523839290705330413 114931114321439734014498905)
      ·
        refine ⟨86198335741079800510874179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114931114321439734014498905 86198335741079800510874179)
        ·
          refine ⟨129297503611619700766311269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86198335741079800510874179 129297503611619700766311269)
          ·
            refine ⟨24243281927178693893683363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129297503611619700766311269 24243281927178693893683363)
            ·
              refine ⟨36364922890768040840525045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24243281927178693893683363 36364922890768040840525045)
              ·
                refine ⟨3409211521009503828799223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36364922890768040840525045 3409211521009503828799223)
                ·
                  refine ⟨5113817281514255743198835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3409211521009503828799223 5113817281514255743198835)
                  ·
                    refine ⟨7670725922271383614798253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5113817281514255743198835 7670725922271383614798253)
                    ·
                      refine ⟨2876522220851768855549345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7670725922271383614798253 2876522220851768855549345)
                      ·
                        rfl

theorem cell23_5602007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 5, 1, 1, 3].length) (baseStart_5602007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602007 prefixEnd_5602007 := by exact prefixLift 5602007
  have htrace : WordTrace (prefixWord ++ tailWord_5602007) baseStart_5602007 baseEnd_5602007 := by
    simpa [prefixWord, tailWord_5602007, baseEnd_5602007] using wordTrace_append hprefix tailTrace_5602007
  have hstable : (prefixWord ++ tailWord_5602007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602007).length < 2 ^ (prefixWord ++ tailWord_5602007).sum := by decide
  have hdescent : baseEnd_5602007 < baseStart_5602007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602033 : List Nat := [1, 2, 2, 2, 2, 2, 3, 2, 1, 1, 5]
def baseStart_5602033 : Nat := 118140960795 + 5602033 * 2 ^ 59
def prefixEnd_5602033 : Nat := 4983230072969 + 3 ^ 40 * 5602033 * 2
def baseEnd_5602033 : Nat := 2876535571348785753824225

theorem tailTrace_5602033 : CollatzResearch.WordTrace tailWord_5602033 prefixEnd_5602033 2876535571348785753824225 := by
  unfold tailWord_5602033
  simp only [CollatzResearch.WordTrace]
  refine ⟨204322929313798666910666753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136215286209199111273777835 204322929313798666910666753)
  ·
    refine ⟨153242196985349000183000065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204322929313798666910666753 153242196985349000183000065)
    ·
      refine ⟨114931647739011750137250049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153242196985349000183000065 114931647739011750137250049)
      ·
        refine ⟨86198735804258812602937537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114931647739011750137250049 86198735804258812602937537)
        ·
          refine ⟨64649051853194109452203153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86198735804258812602937537 64649051853194109452203153)
          ·
            refine ⟨48486788889895582089152365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64649051853194109452203153 48486788889895582089152365)
            ·
              refine ⟨18182545833710843283432137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48486788889895582089152365 18182545833710843283432137)
              ·
                refine ⟨13636909375283132462574103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18182545833710843283432137 13636909375283132462574103)
                ·
                  refine ⟨20455364062924698693861155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13636909375283132462574103 20455364062924698693861155)
                  ·
                    refine ⟨30683046094387048040791733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20455364062924698693861155 30683046094387048040791733)
                    ·
                      refine ⟨2876535571348785753824225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30683046094387048040791733 2876535571348785753824225)
                      ·
                        rfl

theorem cell23_5602033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_5602033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602033 prefixEnd_5602033 := by exact prefixLift 5602033
  have htrace : WordTrace (prefixWord ++ tailWord_5602033) baseStart_5602033 baseEnd_5602033 := by
    simpa [prefixWord, tailWord_5602033, baseEnd_5602033] using wordTrace_append hprefix tailTrace_5602033
  have hstable : (prefixWord ++ tailWord_5602033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602033).length < 2 ^ (prefixWord ++ tailWord_5602033).sum := by decide
  have hdescent : baseEnd_5602033 < baseStart_5602033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602063 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 3, 3, 3]
def baseStart_5602063 : Nat := 118140960795 + 5602063 * 2 ^ 59
def prefixEnd_5602063 : Nat := 4983230072969 + 3 ^ 40 * 5602063 * 2
def baseEnd_5602063 : Nat := 2876550975768420636449087

theorem tailTrace_5602063 : CollatzResearch.WordTrace tailWord_5602063 prefixEnd_5602063 2876550975768420636449087 := by
  unfold tailWord_5602063
  simp only [CollatzResearch.WordTrace]
  refine ⟨204324023503689982034258843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136216015669126654689505895 204324023503689982034258843)
  ·
    refine ⟨306486035255534973051388265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204324023503689982034258843 306486035255534973051388265)
    ·
      refine ⟨229864526441651229788541199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306486035255534973051388265 229864526441651229788541199)
      ·
        refine ⟨344796789662476844682811799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229864526441651229788541199 344796789662476844682811799)
        ·
          refine ⟨517195184493715267024217699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344796789662476844682811799 517195184493715267024217699)
          ·
            refine ⟨775792776740572900536326549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 517195184493715267024217699 775792776740572900536326549)
            ·
              refine ⟨36365286409714354712640307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 775792776740572900536326549 36365286409714354712640307)
              ·
                refine ⟨54547929614571532068960461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36365286409714354712640307 54547929614571532068960461)
                ·
                  refine ⟨20455473605464324525860173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54547929614571532068960461 20455473605464324525860173)
                  ·
                    refine ⟨7670802602049121697197565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20455473605464324525860173 7670802602049121697197565)
                    ·
                      refine ⟨2876550975768420636449087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7670802602049121697197565 2876550975768420636449087)
                      ·
                        rfl

theorem cell23_5602063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 3, 3].length) (baseStart_5602063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602063 prefixEnd_5602063 := by exact prefixLift 5602063
  have htrace : WordTrace (prefixWord ++ tailWord_5602063) baseStart_5602063 baseEnd_5602063 := by
    simpa [prefixWord, tailWord_5602063, baseEnd_5602063] using wordTrace_append hprefix tailTrace_5602063
  have hstable : (prefixWord ++ tailWord_5602063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602063).length < 2 ^ (prefixWord ++ tailWord_5602063).sum := by decide
  have hdescent : baseEnd_5602063 < baseStart_5602063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602081 : List Nat := [1, 2, 3, 2, 1, 2, 5, 2, 1, 2, 2]
def baseStart_5602081 : Nat := 118140960795 + 5602081 * 2 ^ 59
def prefixEnd_5602081 : Nat := 4983230072969 + 3 ^ 40 * 5602081 * 2
def baseEnd_5602081 : Nat := 2876560218420201566024005

theorem tailTrace_5602081 : CollatzResearch.WordTrace tailWord_5602081 prefixEnd_5602081 2876560218420201566024005 := by
  unfold tailWord_5602081
  simp only [CollatzResearch.WordTrace]
  refine ⟨204324680017624771108414097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136216453345083180738942731 204324680017624771108414097)
  ·
    refine ⟨153243510013218578331310573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204324680017624771108414097 153243510013218578331310573)
    ·
      refine ⟨57466316254956966874241465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153243510013218578331310573 57466316254956966874241465)
      ·
        refine ⟨43099737191217725155681099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57466316254956966874241465 43099737191217725155681099)
        ·
          refine ⟨64649605786826587733521649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43099737191217725155681099 64649605786826587733521649)
          ·
            refine ⟨48487204340119940800141237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64649605786826587733521649 48487204340119940800141237)
            ·
              refine ⟨4545675406886244450013241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48487204340119940800141237 4545675406886244450013241)
              ·
                refine ⟨3409256555164683337509931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4545675406886244450013241 3409256555164683337509931)
                ·
                  refine ⟨5113884832747025006264897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3409256555164683337509931 5113884832747025006264897)
                  ·
                    refine ⟨3835413624560268754698673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5113884832747025006264897 3835413624560268754698673)
                    ·
                      refine ⟨2876560218420201566024005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3835413624560268754698673 2876560218420201566024005)
                      ·
                        rfl

theorem cell23_5602081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_5602081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602081 prefixEnd_5602081 := by exact prefixLift 5602081
  have htrace : WordTrace (prefixWord ++ tailWord_5602081) baseStart_5602081 baseEnd_5602081 := by
    simpa [prefixWord, tailWord_5602081, baseEnd_5602081] using wordTrace_append hprefix tailTrace_5602081
  have hstable : (prefixWord ++ tailWord_5602081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602081).length < 2 ^ (prefixWord ++ tailWord_5602081).sum := by decide
  have hdescent : baseEnd_5602081 < baseStart_5602081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602097 : List Nat := [1, 2, 2, 3, 2, 1, 3, 3, 2, 1, 3]
def baseStart_5602097 : Nat := 118140960795 + 5602097 * 2 ^ 59
def prefixEnd_5602097 : Nat := 4983230072969 + 3 ^ 40 * 5602097 * 2
def baseEnd_5602097 : Nat := 2876568434110673503423931

theorem tailTrace_5602097 : CollatzResearch.WordTrace tailWord_5602097 prefixEnd_5602097 2876568434110673503423931 := by
  unfold tailWord_5602097
  simp only [CollatzResearch.WordTrace]
  refine ⟨204325263585566805840996545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136216842390377870560664363 204325263585566805840996545)
  ·
    refine ⟨153243947689175104380747409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204325263585566805840996545 153243947689175104380747409)
    ·
      refine ⟨114932960766881328285560557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153243947689175104380747409 114932960766881328285560557)
      ·
        refine ⟨43099860287580498107085209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114932960766881328285560557 43099860287580498107085209)
        ·
          refine ⟨32324895215685373580313907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43099860287580498107085209 32324895215685373580313907)
          ·
            refine ⟨48487342823528060370470861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32324895215685373580313907 48487342823528060370470861)
            ·
              refine ⟨18182753558823022638926573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48487342823528060370470861 18182753558823022638926573)
              ·
                refine ⟨6818532584558633489597465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18182753558823022638926573 6818532584558633489597465)
                ·
                  refine ⟨5113899438418975117198099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6818532584558633489597465 5113899438418975117198099)
                  ·
                    refine ⟨7670849157628462675797149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5113899438418975117198099 7670849157628462675797149)
                    ·
                      refine ⟨2876568434110673503423931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7670849157628462675797149 2876568434110673503423931)
                      ·
                        rfl

theorem cell23_5602097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_5602097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602097 prefixEnd_5602097 := by exact prefixLift 5602097
  have htrace : WordTrace (prefixWord ++ tailWord_5602097) baseStart_5602097 baseEnd_5602097 := by
    simpa [prefixWord, tailWord_5602097, baseEnd_5602097] using wordTrace_append hprefix tailTrace_5602097
  have hstable : (prefixWord ++ tailWord_5602097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602097).length < 2 ^ (prefixWord ++ tailWord_5602097).sum := by decide
  have hdescent : baseEnd_5602097 < baseStart_5602097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602118 : List Nat := [6, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3]
def baseStart_5602118 : Nat := 118140960795 + 5602118 * 2 ^ 59
def prefixEnd_5602118 : Nat := 4983230072969 + 3 ^ 40 * 5602118 * 2
def baseEnd_5602118 : Nat := 2876579217204417921261335

theorem tailTrace_5602118 : CollatzResearch.WordTrace tailWord_5602118 prefixEnd_5602118 2876579217204417921261335 := by
  unfold tailWord_5602118
  simp only [CollatzResearch.WordTrace]
  refine ⟨6385188422452835200859719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 136217353012327150951674005 6385188422452835200859719)
  ·
    refine ⟨9577782633679252801289579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6385188422452835200859719 9577782633679252801289579)
    ·
      refine ⟨14366673950518879201934369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9577782633679252801289579 14366673950518879201934369)
      ·
        refine ⟨10775005462889159401450777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14366673950518879201934369 10775005462889159401450777)
        ·
          refine ⟨8081254097166869551088083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10775005462889159401450777 8081254097166869551088083)
          ·
            refine ⟨12121881145750304326632125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8081254097166869551088083 12121881145750304326632125)
            ·
              refine ⟨4545705429656364122487047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12121881145750304326632125 4545705429656364122487047)
              ·
                refine ⟨6818558144484546183730571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4545705429656364122487047 6818558144484546183730571)
                ·
                  refine ⟨10227837216726819275595857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6818558144484546183730571 10227837216726819275595857)
                  ·
                    refine ⟨7670877912545114456696893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10227837216726819275595857 7670877912545114456696893)
                    ·
                      refine ⟨2876579217204417921261335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7670877912545114456696893 2876579217204417921261335)
                      ·
                        rfl

theorem cell23_5602118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_5602118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602118 prefixEnd_5602118 := by exact prefixLift 5602118
  have htrace : WordTrace (prefixWord ++ tailWord_5602118) baseStart_5602118 baseEnd_5602118 := by
    simpa [prefixWord, tailWord_5602118, baseEnd_5602118] using wordTrace_append hprefix tailTrace_5602118
  have hstable : (prefixWord ++ tailWord_5602118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602118).length < 2 ^ (prefixWord ++ tailWord_5602118).sum := by decide
  have hdescent : baseEnd_5602118 < baseStart_5602118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602123 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 6, 4, 3]
def baseStart_5602123 : Nat := 118140960795 + 5602123 * 2 ^ 59
def prefixEnd_5602123 : Nat := 4983230072969 + 3 ^ 40 * 5602123 * 2
def baseEnd_5602123 : Nat := 2876581784607690401698811

theorem tailTrace_5602123 : CollatzResearch.WordTrace tailWord_5602123 prefixEnd_5602123 2876581784607690401698811 := by
  unfold tailWord_5602123
  simp only [CollatzResearch.WordTrace]
  refine ⟨204326211883472612281443023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136217474588981741520962015 204326211883472612281443023)
  ·
    refine ⟨306489317825208918422164535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204326211883472612281443023 306489317825208918422164535)
    ·
      refine ⟨459733976737813377633246803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306489317825208918422164535 459733976737813377633246803)
      ·
        refine ⟨689600965106720066449870205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459733976737813377633246803 689600965106720066449870205)
        ·
          refine ⟨258600361915020024918701327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 689600965106720066449870205 258600361915020024918701327)
          ·
            refine ⟨387900542872530037378051991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258600361915020024918701327 387900542872530037378051991)
            ·
              refine ⟨581850814308795056067077987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387900542872530037378051991 581850814308795056067077987)
              ·
                refine ⟨872776221463192584100616981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 581850814308795056067077987 872776221463192584100616981)
                ·
                  refine ⟨40911385381087152379716421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 872776221463192584100616981 40911385381087152379716421)
                  ·
                    refine ⟨7670884758953841071196829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40911385381087152379716421 7670884758953841071196829)
                    ·
                      refine ⟨2876581784607690401698811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7670884758953841071196829 2876581784607690401698811)
                      ·
                        rfl

theorem cell23_5602123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 4, 3].length) (baseStart_5602123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602123 prefixEnd_5602123 := by exact prefixLift 5602123
  have htrace : WordTrace (prefixWord ++ tailWord_5602123) baseStart_5602123 baseEnd_5602123 := by
    simpa [prefixWord, tailWord_5602123, baseEnd_5602123] using wordTrace_append hprefix tailTrace_5602123
  have hstable : (prefixWord ++ tailWord_5602123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602123).length < 2 ^ (prefixWord ++ tailWord_5602123).sum := by decide
  have hdescent : baseEnd_5602123 < baseStart_5602123 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602143 : List Nat := [1, 1, 2, 3, 1, 3, 2, 3, 7]
def baseStart_5602143 : Nat := 118140960795 + 5602143 * 2 ^ 59
def prefixEnd_5602143 : Nat := 4983230072969 + 3 ^ 40 * 5602143 * 2
def baseEnd_5602143 : Nat := 319621339357864480383191

theorem tailTrace_5602143 : CollatzResearch.WordTrace tailWord_5602143 prefixEnd_5602143 319621339357864480383191 := by
  unfold tailWord_5602143
  simp only [CollatzResearch.WordTrace]
  refine ⟨204326941343400155697171083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136217960895600103798114055 204326941343400155697171083)
  ·
    refine ⟨306490412015100233545756625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204326941343400155697171083 306490412015100233545756625)
    ·
      refine ⟨229867809011325175159317469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306490412015100233545756625 229867809011325175159317469)
      ·
        refine ⟨86200428379246940684744051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229867809011325175159317469 86200428379246940684744051)
        ·
          refine ⟨129300642568870411027116077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86200428379246940684744051 129300642568870411027116077)
          ·
            refine ⟨48487740963326404135168529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129300642568870411027116077 48487740963326404135168529)
            ·
              refine ⟨36365805722494803101376397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48487740963326404135168529 36365805722494803101376397)
              ·
                refine ⟨13637177145935551163016149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36365805722494803101376397 13637177145935551163016149)
                ·
                  refine ⟨319621339357864480383191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13637177145935551163016149 319621339357864480383191)
                  ·
                    rfl

theorem cell23_5602143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 7].length) (baseStart_5602143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602143 prefixEnd_5602143 := by exact prefixLift 5602143
  have htrace : WordTrace (prefixWord ++ tailWord_5602143) baseStart_5602143 baseEnd_5602143 := by
    simpa [prefixWord, tailWord_5602143, baseEnd_5602143] using wordTrace_append hprefix tailTrace_5602143
  have hstable : (prefixWord ++ tailWord_5602143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602143).length < 2 ^ (prefixWord ++ tailWord_5602143).sum := by decide
  have hdescent : baseEnd_5602143 < baseStart_5602143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602223 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 6]
def baseStart_5602223 : Nat := 118140960795 + 5602223 * 2 ^ 59
def prefixEnd_5602223 : Nat := 4983230072969 + 3 ^ 40 * 5602223 * 2
def baseEnd_5602223 : Nat := 2876633132673140010448351

theorem tailTrace_5602223 : CollatzResearch.WordTrace tailWord_5602223 prefixEnd_5602223 2876633132673140010448351 := by
  unfold tailWord_5602223
  simp only [CollatzResearch.WordTrace]
  refine ⟨204329859183110329360083323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136219906122073552906722215 204329859183110329360083323)
  ·
    refine ⟨306494788774665494040124985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204329859183110329360083323 306494788774665494040124985)
    ·
      refine ⟨229871091580999120530093739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306494788774665494040124985 229871091580999120530093739)
      ·
        refine ⟨344806637371498680795140609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229871091580999120530093739 344806637371498680795140609)
        ·
          refine ⟨258604978028624010596355457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344806637371498680795140609 258604978028624010596355457)
          ·
            refine ⟨193953733521468007947266593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258604978028624010596355457 193953733521468007947266593)
            ·
              refine ⟨145465300141101005960449945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193953733521468007947266593 145465300141101005960449945)
              ·
                refine ⟨109098975105825754470337459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145465300141101005960449945 109098975105825754470337459)
                ·
                  refine ⟨163648462658738631705506189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109098975105825754470337459 163648462658738631705506189)
                  ·
                    refine ⟨61368173497026986889564821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 163648462658738631705506189 61368173497026986889564821)
                    ·
                      refine ⟨2876633132673140010448351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61368173497026986889564821 2876633132673140010448351)
                      ·
                        rfl

theorem cell23_5602223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 6].length) (baseStart_5602223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602223 prefixEnd_5602223 := by exact prefixLift 5602223
  have htrace : WordTrace (prefixWord ++ tailWord_5602223) baseStart_5602223 baseEnd_5602223 := by
    simpa [prefixWord, tailWord_5602223, baseEnd_5602223] using wordTrace_append hprefix tailTrace_5602223
  have hstable : (prefixWord ++ tailWord_5602223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602223).length < 2 ^ (prefixWord ++ tailWord_5602223).sum := by decide
  have hdescent : baseEnd_5602223 < baseStart_5602223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602250 : List Nat := [3, 1, 2, 1, 2, 1, 1, 6, 6]
def baseStart_5602250 : Nat := 118140960795 + 5602250 * 2 ^ 59
def prefixEnd_5602250 : Nat := 4983230072969 + 3 ^ 40 * 5602250 * 2
def baseEnd_5602250 : Nat := 319627444072312378312303

theorem tailTrace_5602250 : CollatzResearch.WordTrace tailWord_5602250 prefixEnd_5602250 319627444072312378312303 := by
  unfold tailWord_5602250
  simp only [CollatzResearch.WordTrace]
  refine ⟨51082710988503128242829051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136220562636008341980877469 51082710988503128242829051)
  ·
    refine ⟨76624066482754692364243577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51082710988503128242829051 76624066482754692364243577)
    ·
      refine ⟨57468049862066019273182683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76624066482754692364243577 57468049862066019273182683)
      ·
        refine ⟨86202074793099028909774025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57468049862066019273182683 86202074793099028909774025)
        ·
          refine ⟨64651556094824271682330519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86202074793099028909774025 64651556094824271682330519)
          ·
            refine ⟨96977334142236407523495779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64651556094824271682330519 96977334142236407523495779)
            ·
              refine ⟨145466001213354611285243669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96977334142236407523495779 145466001213354611285243669)
              ·
                refine ⟨6818718806875997403995797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 145466001213354611285243669 6818718806875997403995797)
                ·
                  refine ⟨319627444072312378312303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6818718806875997403995797 319627444072312378312303)
                  ·
                    rfl

theorem cell23_5602250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 6].length) (baseStart_5602250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602250 prefixEnd_5602250 := by exact prefixLift 5602250
  have htrace : WordTrace (prefixWord ++ tailWord_5602250) baseStart_5602250 baseEnd_5602250 := by
    simpa [prefixWord, tailWord_5602250, baseEnd_5602250] using wordTrace_append hprefix tailTrace_5602250
  have hstable : (prefixWord ++ tailWord_5602250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602250).length < 2 ^ (prefixWord ++ tailWord_5602250).sum := by decide
  have hdescent : baseEnd_5602250 < baseStart_5602250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602254 : List Nat := [4, 1, 1, 1, 2, 5, 1, 1, 3, 4]
def baseStart_5602254 : Nat := 118140960795 + 5602254 * 2 ^ 59
def prefixEnd_5602254 : Nat := 4983230072969 + 3 ^ 40 * 5602254 * 2
def baseEnd_5602254 : Nat := 958883016857809796386903

theorem tailTrace_5602254 : CollatzResearch.WordTrace tailWord_5602254 prefixEnd_5602254 958883016857809796386903 := by
  unfold tailWord_5602254
  simp only [CollatzResearch.WordTrace]
  refine ⟨25541373730749752706807727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136220659897332014436307877 25541373730749752706807727)
  ·
    refine ⟨38312060596124629060211591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25541373730749752706807727 38312060596124629060211591)
    ·
      refine ⟨57468090894186943590317387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38312060596124629060211591 57468090894186943590317387)
      ·
        refine ⟨86202136341280415385476081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57468090894186943590317387 86202136341280415385476081)
        ·
          refine ⟨64651602255960311539107061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86202136341280415385476081 64651602255960311539107061)
          ·
            refine ⟨6061087711496279206791287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64651602255960311539107061 6061087711496279206791287)
            ·
              refine ⟨9091631567244418810186931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6061087711496279206791287 9091631567244418810186931)
              ·
                refine ⟨13637447350866628215280397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9091631567244418810186931 13637447350866628215280397)
                ·
                  refine ⟨5114042756574985580730149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13637447350866628215280397 5114042756574985580730149)
                  ·
                    refine ⟨958883016857809796386903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5114042756574985580730149 958883016857809796386903)
                    ·
                      rfl

theorem cell23_5602254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_5602254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602254 prefixEnd_5602254 := by exact prefixLift 5602254
  have htrace : WordTrace (prefixWord ++ tailWord_5602254) baseStart_5602254 baseEnd_5602254 := by
    simpa [prefixWord, tailWord_5602254, baseEnd_5602254] using wordTrace_append hprefix tailTrace_5602254
  have hstable : (prefixWord ++ tailWord_5602254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602254).length < 2 ^ (prefixWord ++ tailWord_5602254).sum := by decide
  have hdescent : baseEnd_5602254 < baseStart_5602254 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602311 : List Nat := [1, 1, 4, 3, 1, 1, 3, 4, 1, 1, 3]
def baseStart_5602311 : Nat := 118140960795 + 5602311 * 2 ^ 59
def prefixEnd_5602311 : Nat := 4983230072969 + 3 ^ 40 * 5602311 * 2
def baseEnd_5602311 : Nat := 2876678318970735666147947

theorem tailTrace_5602311 : CollatzResearch.WordTrace tailWord_5602311 prefixEnd_5602311 2876678318970735666147947 := by
  unfold tailWord_5602311
  simp only [CollatzResearch.WordTrace]
  refine ⟨204333068806791520389286787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136222045871194346926191191 204333068806791520389286787)
  ·
    refine ⟨306499603210187280583930181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204333068806791520389286787 306499603210187280583930181)
    ·
      refine ⟨57468675601910115109486909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 306499603210187280583930181 57468675601910115109486909)
      ·
        refine ⟨21550753350716293166057591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57468675601910115109486909 21550753350716293166057591)
        ·
          refine ⟨32326130026074439749086387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21550753350716293166057591 32326130026074439749086387)
          ·
            refine ⟨48489195039111659623629581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32326130026074439749086387 48489195039111659623629581)
            ·
              refine ⟨18183448139666872358861093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48489195039111659623629581 18183448139666872358861093)
              ·
                refine ⟨3409396526187538567286455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18183448139666872358861093 3409396526187538567286455)
                ·
                  refine ⟨5114094789281307850929683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3409396526187538567286455 5114094789281307850929683)
                  ·
                    refine ⟨7671142183921961776394525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5114094789281307850929683 7671142183921961776394525)
                    ·
                      refine ⟨2876678318970735666147947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7671142183921961776394525 2876678318970735666147947)
                      ·
                        rfl

theorem cell23_5602311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_5602311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602311 prefixEnd_5602311 := by exact prefixLift 5602311
  have htrace : WordTrace (prefixWord ++ tailWord_5602311) baseStart_5602311 baseEnd_5602311 := by
    simpa [prefixWord, tailWord_5602311, baseEnd_5602311] using wordTrace_append hprefix tailTrace_5602311
  have hstable : (prefixWord ++ tailWord_5602311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602311).length < 2 ^ (prefixWord ++ tailWord_5602311).sum := by decide
  have hdescent : baseEnd_5602311 < baseStart_5602311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602320 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 3]
def baseStart_5602320 : Nat := 118140960795 + 5602320 * 2 ^ 59
def prefixEnd_5602320 : Nat := 4983230072969 + 3 ^ 40 * 5602320 * 2
def baseEnd_5602320 : Nat := 2876682940296626130935405

theorem tailTrace_5602320 : CollatzResearch.WordTrace tailWord_5602320 prefixEnd_5602320 2876682940296626130935405 := by
  unfold tailWord_5602320
  simp only [CollatzResearch.WordTrace]
  refine ⟨102166698531879457463182207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136222264709172609950909609 102166698531879457463182207)
  ·
    refine ⟨153250047797819186194773311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102166698531879457463182207 153250047797819186194773311)
    ·
      refine ⟨229875071696728779292159967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153250047797819186194773311 229875071696728779292159967)
      ·
        refine ⟨344812607545093168938239951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229875071696728779292159967 344812607545093168938239951)
        ·
          refine ⟨517218911317639753407359927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344812607545093168938239951 517218911317639753407359927)
          ·
            refine ⟨775828366976459630111039891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 517218911317639753407359927 775828366976459630111039891)
            ·
              refine ⟨1163742550464689445166559837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 775828366976459630111039891 1163742550464689445166559837)
              ·
                refine ⟨436403456424258541937459939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1163742550464689445166559837 436403456424258541937459939)
                ·
                  refine ⟨654605184636387812906189909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 436403456424258541937459939 654605184636387812906189909)
                  ·
                    refine ⟨7671154507457669682494413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 654605184636387812906189909 7671154507457669682494413)
                    ·
                      refine ⟨2876682940296626130935405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7671154507457669682494413 2876682940296626130935405)
                      ·
                        rfl

theorem cell23_5602320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 3].length) (baseStart_5602320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602320 prefixEnd_5602320 := by exact prefixLift 5602320
  have htrace : WordTrace (prefixWord ++ tailWord_5602320) baseStart_5602320 baseEnd_5602320 := by
    simpa [prefixWord, tailWord_5602320, baseEnd_5602320] using wordTrace_append hprefix tailTrace_5602320
  have hstable : (prefixWord ++ tailWord_5602320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602320).length < 2 ^ (prefixWord ++ tailWord_5602320).sum := by decide
  have hdescent : baseEnd_5602320 < baseStart_5602320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602327 : List Nat := [1, 1, 3, 5, 1, 1, 1, 3, 1, 6]
def baseStart_5602327 : Nat := 118140960795 + 5602327 * 2 ^ 59
def prefixEnd_5602327 : Nat := 4983230072969 + 3 ^ 40 * 5602327 * 2
def baseEnd_5602327 : Nat := 958895511553735867849291

theorem tailTrace_5602327 : CollatzResearch.WordTrace tailWord_5602327 prefixEnd_5602327 958895511553735867849291 := by
  unfold tailWord_5602327
  simp only [CollatzResearch.WordTrace]
  refine ⟨204333652374733555121869235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136222434916489036747912823 204333652374733555121869235)
  ·
    refine ⟨306500478562100332682803853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204333652374733555121869235 306500478562100332682803853)
    ·
      refine ⟨114937679460787624756051445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306500478562100332682803853 114937679460787624756051445)
      ·
        refine ⟨10775407449448839820879823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 114937679460787624756051445 10775407449448839820879823)
        ·
          refine ⟨16163111174173259731319735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10775407449448839820879823 16163111174173259731319735)
          ·
            refine ⟨24244666761259889596979603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16163111174173259731319735 24244666761259889596979603)
            ·
              refine ⟨36367000141889834395469405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24244666761259889596979603 36367000141889834395469405)
              ·
                refine ⟨13637625053208687898301027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36367000141889834395469405 13637625053208687898301027)
                ·
                  refine ⟨20456437579813031847451541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13637625053208687898301027 20456437579813031847451541)
                  ·
                    refine ⟨958895511553735867849291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20456437579813031847451541 958895511553735867849291)
                    ·
                      rfl

theorem cell23_5602327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 6].length) (baseStart_5602327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602327 prefixEnd_5602327 := by exact prefixLift 5602327
  have htrace : WordTrace (prefixWord ++ tailWord_5602327) baseStart_5602327 baseEnd_5602327 := by
    simpa [prefixWord, tailWord_5602327, baseEnd_5602327] using wordTrace_append hprefix tailTrace_5602327
  have hstable : (prefixWord ++ tailWord_5602327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602327).length < 2 ^ (prefixWord ++ tailWord_5602327).sum := by decide
  have hdescent : baseEnd_5602327 < baseStart_5602327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602354 : List Nat := [3, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3]
def baseStart_5602354 : Nat := 118140960795 + 5602354 * 2 ^ 59
def prefixEnd_5602354 : Nat := 4983230072969 + 3 ^ 40 * 5602354 * 2
def baseEnd_5602354 : Nat := 2876700398638878997910249

theorem tailTrace_5602354 : CollatzResearch.WordTrace tailWord_5602354 prefixEnd_5602354 2876700398638878997910249 := by
  unfold tailWord_5602354
  simp only [CollatzResearch.WordTrace]
  refine ⟨51083659286408934683275529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136223091430423825822068077 51083659286408934683275529)
  ·
    refine ⟨38312744464806701012456647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51083659286408934683275529 38312744464806701012456647)
    ·
      refine ⟨57469116697210051518684971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38312744464806701012456647 57469116697210051518684971)
      ·
        refine ⟨86203675045815077278027457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57469116697210051518684971 86203675045815077278027457)
        ·
          refine ⟨64652756284361307958520593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86203675045815077278027457 64652756284361307958520593)
          ·
            refine ⟨48489567213270980968890445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64652756284361307958520593 48489567213270980968890445)
            ·
              refine ⟨18183587704976617863333917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48489567213270980968890445 18183587704976617863333917)
              ·
                refine ⟨6818845389366231698750219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18183587704976617863333917 6818845389366231698750219)
                ·
                  refine ⟨10228268084049347548125329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6818845389366231698750219 10228268084049347548125329)
                  ·
                    refine ⟨7671201063037010661093997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10228268084049347548125329 7671201063037010661093997)
                    ·
                      refine ⟨2876700398638878997910249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7671201063037010661093997 2876700398638878997910249)
                      ·
                        rfl

theorem cell23_5602354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_5602354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602354 prefixEnd_5602354 := by exact prefixLift 5602354
  have htrace : WordTrace (prefixWord ++ tailWord_5602354) baseStart_5602354 baseEnd_5602354 := by
    simpa [prefixWord, tailWord_5602354, baseEnd_5602354] using wordTrace_append hprefix tailTrace_5602354
  have hstable : (prefixWord ++ tailWord_5602354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602354).length < 2 ^ (prefixWord ++ tailWord_5602354).sum := by decide
  have hdescent : baseEnd_5602354 < baseStart_5602354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602361 : List Nat := [1, 2, 1, 5, 2, 3, 1, 2, 2, 4]
def baseStart_5602361 : Nat := 118140960795 + 5602361 * 2 ^ 59
def prefixEnd_5602361 : Nat := 4983230072969 + 3 ^ 40 * 5602361 * 2
def baseEnd_5602361 : Nat := 958901331001153490174239

theorem tailTrace_5602361 : CollatzResearch.WordTrace tailWord_5602361 prefixEnd_5602361 958901331001153490174239 := by
  unfold tailWord_5602361
  simp only [CollatzResearch.WordTrace]
  refine ⟨204334892456610378928606937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136223261637740252619071291 204334892456610378928606937)
  ·
    refine ⟨153251169342457784196455203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204334892456610378928606937 153251169342457784196455203)
    ·
      refine ⟨229876754013686676294682805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153251169342457784196455203 229876754013686676294682805)
      ·
        refine ⟨21550945688783125902626513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 229876754013686676294682805 21550945688783125902626513)
        ·
          refine ⟨16163209266587344426969885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21550945688783125902626513 16163209266587344426969885)
          ·
            refine ⟨6061203474970254160113707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16163209266587344426969885 6061203474970254160113707)
            ·
              refine ⟨9091805212455381240170561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6061203474970254160113707 9091805212455381240170561)
              ·
                refine ⟨6818853909341535930127921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9091805212455381240170561 6818853909341535930127921)
                ·
                  refine ⟨5114140432006151947595941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6818853909341535930127921 5114140432006151947595941)
                  ·
                    refine ⟨958901331001153490174239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5114140432006151947595941 958901331001153490174239)
                    ·
                      rfl

theorem cell23_5602361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 2, 4].length) (baseStart_5602361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602361 prefixEnd_5602361 := by exact prefixLift 5602361
  have htrace : WordTrace (prefixWord ++ tailWord_5602361) baseStart_5602361 baseEnd_5602361 := by
    simpa [prefixWord, tailWord_5602361, baseEnd_5602361] using wordTrace_append hprefix tailTrace_5602361
  have hstable : (prefixWord ++ tailWord_5602361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602361).length < 2 ^ (prefixWord ++ tailWord_5602361).sum := by decide
  have hdescent : baseEnd_5602361 < baseStart_5602361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602377 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 2, 7, 2]
def baseStart_5602377 : Nat := 118140960795 + 5602377 * 2 ^ 59
def prefixEnd_5602377 : Nat := 4983230072969 + 3 ^ 40 * 5602377 * 2
def baseEnd_5602377 : Nat := 2876712208693932407922643

theorem tailTrace_5602377 : CollatzResearch.WordTrace tailWord_5602377 prefixEnd_5602377 2876712208693932407922643 := by
  unfold tailWord_5602377
  simp only [CollatzResearch.WordTrace]
  refine ⟨204335476024552413661189385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136223650683034942440792923 204335476024552413661189385)
  ·
    refine ⟨153251607018414310245892039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204335476024552413661189385 153251607018414310245892039)
    ·
      refine ⟨229877410527621465368838059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153251607018414310245892039 229877410527621465368838059)
      ·
        refine ⟨344816115791432198053257089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229877410527621465368838059 344816115791432198053257089)
        ·
          refine ⟨258612086843574148539942817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344816115791432198053257089 258612086843574148539942817)
          ·
            refine ⟨193959065132680611404957113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258612086843574148539942817 193959065132680611404957113)
            ·
              refine ⟨145469298849510458553717835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193959065132680611404957113 145469298849510458553717835)
              ·
                refine ⟨218203948274265687830576753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145469298849510458553717835 218203948274265687830576753)
                ·
                  refine ⟨163652961205699265872932565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 218203948274265687830576753 163652961205699265872932565)
                  ·
                    refine ⟨3835616278258576543896857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 163652961205699265872932565 3835616278258576543896857)
                    ·
                      refine ⟨2876712208693932407922643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3835616278258576543896857 2876712208693932407922643)
                      ·
                        rfl

theorem cell23_5602377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 7, 2].length) (baseStart_5602377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602377 prefixEnd_5602377 := by exact prefixLift 5602377
  have htrace : WordTrace (prefixWord ++ tailWord_5602377) baseStart_5602377 baseEnd_5602377 := by
    simpa [prefixWord, tailWord_5602377, baseEnd_5602377] using wordTrace_append hprefix tailTrace_5602377
  have hstable : (prefixWord ++ tailWord_5602377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602377).length < 2 ^ (prefixWord ++ tailWord_5602377).sum := by decide
  have hdescent : baseEnd_5602377 < baseStart_5602377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602381 : List Nat := [1, 6, 1, 1, 1, 4, 1, 1, 1, 2, 4]
def baseStart_5602381 : Nat := 118140960795 + 5602381 * 2 ^ 59
def prefixEnd_5602381 : Nat := 4983230072969 + 3 ^ 40 * 5602381 * 2
def baseEnd_5602381 : Nat := 2876714262616550392272625

theorem tailTrace_5602381 : CollatzResearch.WordTrace tailWord_5602381 prefixEnd_5602381 2876714262616550392272625 := by
  unfold tailWord_5602381
  simp only [CollatzResearch.WordTrace]
  refine ⟨204335621916537922344334997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136223747944358614896223331 204335621916537922344334997)
  ·
    refine ⟨9578232277337715109890703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 204335621916537922344334997 9578232277337715109890703)
    ·
      refine ⟨14367348416006572664836055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9578232277337715109890703 14367348416006572664836055)
      ·
        refine ⟨21551022624009858997254083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14367348416006572664836055 21551022624009858997254083)
        ·
          refine ⟨32326533936014788495881125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21551022624009858997254083 32326533936014788495881125)
          ·
            refine ⟨6061225113002772842977711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32326533936014788495881125 6061225113002772842977711)
            ·
              refine ⟨9091837669504159264466567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6061225113002772842977711 9091837669504159264466567)
              ·
                refine ⟨13637756504256238896699851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9091837669504159264466567 13637756504256238896699851)
                ·
                  refine ⟨20456634756384358345049777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13637756504256238896699851 20456634756384358345049777)
                  ·
                    refine ⟨15342476067288268758787333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20456634756384358345049777 15342476067288268758787333)
                    ·
                      refine ⟨2876714262616550392272625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15342476067288268758787333 2876714262616550392272625)
                      ·
                        rfl

theorem cell23_5602381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_5602381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602381 prefixEnd_5602381 := by exact prefixLift 5602381
  have htrace : WordTrace (prefixWord ++ tailWord_5602381) baseStart_5602381 baseEnd_5602381 := by
    simpa [prefixWord, tailWord_5602381, baseEnd_5602381] using wordTrace_append hprefix tailTrace_5602381
  have hstable : (prefixWord ++ tailWord_5602381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602381).length < 2 ^ (prefixWord ++ tailWord_5602381).sum := by decide
  have hdescent : baseEnd_5602381 < baseStart_5602381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602384 : List Nat := [2, 1, 1, 1, 1, 3, 1, 7, 2, 1, 3]
def baseStart_5602384 : Nat := 118140960795 + 5602384 * 2 ^ 59
def prefixEnd_5602384 : Nat := 4983230072969 + 3 ^ 40 * 5602384 * 2
def baseEnd_5602384 : Nat := 2876715803058513880535111

theorem tailTrace_5602384 : CollatzResearch.WordTrace tailWord_5602384 prefixEnd_5602384 2876715803058513880535111 := by
  unfold tailWord_5602384
  simp only [CollatzResearch.WordTrace]
  refine ⟨102167865667763526928347103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136223820890351369237796137 102167865667763526928347103)
  ·
    refine ⟨153251798501645290392520655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102167865667763526928347103 153251798501645290392520655)
    ·
      refine ⟨229877697752467935588780983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153251798501645290392520655 229877697752467935588780983)
      ·
        refine ⟨344816546628701903383171475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229877697752467935588780983 344816546628701903383171475)
        ·
          refine ⟨517224819943052855074757213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344816546628701903383171475 517224819943052855074757213)
          ·
            refine ⟨193959307478644820653033955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 517224819943052855074757213 193959307478644820653033955)
            ·
              refine ⟨290938961217967230979550933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193959307478644820653033955 290938961217967230979550933)
              ·
                refine ⟨6818881903546106976083225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 290938961217967230979550933 6818881903546106976083225)
                ·
                  refine ⟨5114161427659580232062419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6818881903546106976083225 5114161427659580232062419)
                  ·
                    refine ⟨7671242141489370348093629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5114161427659580232062419 7671242141489370348093629)
                    ·
                      refine ⟨2876715803058513880535111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7671242141489370348093629 2876715803058513880535111)
                      ·
                        rfl

theorem cell23_5602384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 2, 1, 3].length) (baseStart_5602384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602384 prefixEnd_5602384 := by exact prefixLift 5602384
  have htrace : WordTrace (prefixWord ++ tailWord_5602384) baseStart_5602384 baseEnd_5602384 := by
    simpa [prefixWord, tailWord_5602384, baseEnd_5602384] using wordTrace_append hprefix tailTrace_5602384
  have hstable : (prefixWord ++ tailWord_5602384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602384).length < 2 ^ (prefixWord ++ tailWord_5602384).sum := by decide
  have hdescent : baseEnd_5602384 < baseStart_5602384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602402 : List Nat := [3, 3, 2, 2, 1, 3, 1, 3, 1, 2, 2]
def baseStart_5602402 : Nat := 118140960795 + 5602402 * 2 ^ 59
def prefixEnd_5602402 : Nat := 4983230072969 + 3 ^ 40 * 5602402 * 2
def baseEnd_5602402 : Nat := 2876725045710294810110029

theorem tailTrace_5602402 : CollatzResearch.WordTrace tailWord_5602402 prefixEnd_5602402 2876725045710294810110029 := by
  unfold tailWord_5602402
  simp only [CollatzResearch.WordTrace]
  refine ⟨51084096962365460732712365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136224258566307895287232973 51084096962365460732712365)
  ·
    refine ⟨19156536360887047774767137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51084096962365460732712365 19156536360887047774767137)
    ·
      refine ⟨14367402270665285831075353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19156536360887047774767137 14367402270665285831075353)
      ·
        refine ⟨10775551702998964373306515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14367402270665285831075353 10775551702998964373306515)
        ·
          refine ⟨16163327554498446559959773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10775551702998964373306515 16163327554498446559959773)
          ·
            refine ⟨6061247832936917459984915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16163327554498446559959773 6061247832936917459984915)
            ·
              refine ⟨9091871749405376189977373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6061247832936917459984915 9091871749405376189977373)
              ·
                refine ⟨3409451906027016071241515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9091871749405376189977373 3409451906027016071241515)
                ·
                  refine ⟨5114177859040524106862273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3409451906027016071241515 5114177859040524106862273)
                  ·
                    refine ⟨3835633394280393080146705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5114177859040524106862273 3835633394280393080146705)
                    ·
                      refine ⟨2876725045710294810110029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3835633394280393080146705 2876725045710294810110029)
                      ·
                        rfl

theorem cell23_5602402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_5602402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602402 prefixEnd_5602402 := by exact prefixLift 5602402
  have htrace : WordTrace (prefixWord ++ tailWord_5602402) baseStart_5602402 baseEnd_5602402 := by
    simpa [prefixWord, tailWord_5602402, baseEnd_5602402] using wordTrace_append hprefix tailTrace_5602402
  have hstable : (prefixWord ++ tailWord_5602402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602402).length < 2 ^ (prefixWord ++ tailWord_5602402).sum := by decide
  have hdescent : baseEnd_5602402 < baseStart_5602402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602457 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 6, 3, 3]
def baseStart_5602457 : Nat := 118140960795 + 5602457 * 2 ^ 59
def prefixEnd_5602457 : Nat := 4983230072969 + 3 ^ 40 * 5602457 * 2
def baseEnd_5602457 : Nat := 2876753287146292094922275

theorem tailTrace_5602457 : CollatzResearch.WordTrace tailWord_5602457 prefixEnd_5602457 2876753287146292094922275 := by
  unfold tailWord_5602457
  simp only [CollatzResearch.WordTrace]
  refine ⟨204338393864262587324101625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136225595909508391549401083 204338393864262587324101625)
  ·
    refine ⟨153253795398196940493076219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204338393864262587324101625 153253795398196940493076219)
    ·
      refine ⟨229880693097295410739614329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153253795398196940493076219 229880693097295410739614329)
      ·
        refine ⟨172410519822971558054710747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229880693097295410739614329 172410519822971558054710747)
        ·
          refine ⟨258615779734457337082066121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172410519822971558054710747 258615779734457337082066121)
          ·
            refine ⟨193961834800843002811549591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258615779734457337082066121 193961834800843002811549591)
            ·
              refine ⟨290942752201264504217324387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193961834800843002811549591 290942752201264504217324387)
              ·
                refine ⟨436414128301896756325986581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290942752201264504217324387 436414128301896756325986581)
                ·
                  refine ⟨20456912264151410452780621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 436414128301896756325986581 20456912264151410452780621)
                  ·
                    refine ⟨7671342099056778919792733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20456912264151410452780621 7671342099056778919792733)
                    ·
                      refine ⟨2876753287146292094922275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7671342099056778919792733 2876753287146292094922275)
                      ·
                        rfl

theorem cell23_5602457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 3, 3].length) (baseStart_5602457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602457 prefixEnd_5602457 := by exact prefixLift 5602457
  have htrace : WordTrace (prefixWord ++ tailWord_5602457) baseStart_5602457 baseEnd_5602457 := by
    simpa [prefixWord, tailWord_5602457, baseEnd_5602457] using wordTrace_append hprefix tailTrace_5602457
  have hstable : (prefixWord ++ tailWord_5602457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602457).length < 2 ^ (prefixWord ++ tailWord_5602457).sum := by decide
  have hdescent : baseEnd_5602457 < baseStart_5602457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602464 : List Nat := [2, 1, 1, 4, 2, 1, 2, 5, 5]
def baseStart_5602464 : Nat := 118140960795 + 5602464 * 2 ^ 59
def prefixEnd_5602464 : Nat := 4983230072969 + 3 ^ 40 * 5602464 * 2
def baseEnd_5602464 : Nat := 319639653501208174170527

theorem tailTrace_5602464 : CollatzResearch.WordTrace tailWord_5602464 prefixEnd_5602464 319639653501208174170527 := by
  unfold tailWord_5602464
  simp only [CollatzResearch.WordTrace]
  refine ⟨102169324587618613759803223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136225766116824818346404297 102169324587618613759803223)
  ·
    refine ⟨153253986881427920639704835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102169324587618613759803223 153253986881427920639704835)
    ·
      refine ⟨229880980322141880959557253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153253986881427920639704835 229880980322141880959557253)
      ·
        refine ⟨43102683810401602679916985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 229880980322141880959557253 43102683810401602679916985)
        ·
          refine ⟨32327012857801202009937739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43102683810401602679916985 32327012857801202009937739)
          ·
            refine ⟨48490519286701803014906609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32327012857801202009937739 48490519286701803014906609)
            ·
              refine ⟨36367889465026352261179957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48490519286701803014906609 36367889465026352261179957)
              ·
                refine ⟨3409489637346220524485621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36367889465026352261179957 3409489637346220524485621)
                ·
                  refine ⟨319639653501208174170527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3409489637346220524485621 319639653501208174170527)
                  ·
                    rfl

theorem cell23_5602464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 5, 5].length) (baseStart_5602464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602464 prefixEnd_5602464 := by exact prefixLift 5602464
  have htrace : WordTrace (prefixWord ++ tailWord_5602464) baseStart_5602464 baseEnd_5602464 := by
    simpa [prefixWord, tailWord_5602464, baseEnd_5602464] using wordTrace_append hprefix tailTrace_5602464
  have hstable : (prefixWord ++ tailWord_5602464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602464).length < 2 ^ (prefixWord ++ tailWord_5602464).sum := by decide
  have hdescent : baseEnd_5602464 < baseStart_5602464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602481 : List Nat := [1, 2, 2, 5, 1, 2, 1, 4, 5]
def baseStart_5602481 : Nat := 118140960795 + 5602481 * 2 ^ 59
def prefixEnd_5602481 : Nat := 4983230072969 + 3 ^ 40 * 5602481 * 2
def baseEnd_5602481 : Nat := 319640623409111111224685

theorem tailTrace_5602481 : CollatzResearch.WordTrace tailWord_5602481 prefixEnd_5602481 319640623409111111224685 := by
  unfold tailWord_5602481
  simp only [CollatzResearch.WordTrace]
  refine ⟨204339269216175639422975297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136226179477450426281983531 204339269216175639422975297)
  ·
    refine ⟨153254451912131729567231473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204339269216175639422975297 153254451912131729567231473)
    ·
      refine ⟨114940838934098797175423605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153254451912131729567231473 114940838934098797175423605)
      ·
        refine ⟨10775703650071762235195963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 114940838934098797175423605 10775703650071762235195963)
        ·
          refine ⟨16163555475107643352793945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10775703650071762235195963 16163555475107643352793945)
          ·
            refine ⟨12122666606330732514595459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16163555475107643352793945 12122666606330732514595459)
            ·
              refine ⟨18183999909496098771893189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12122666606330732514595459 18183999909496098771893189)
              ·
                refine ⟨3409499983030518519729973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18183999909496098771893189 3409499983030518519729973)
                ·
                  refine ⟨319640623409111111224685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3409499983030518519729973 319640623409111111224685)
                  ·
                    rfl

theorem cell23_5602481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 4, 5].length) (baseStart_5602481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602481 prefixEnd_5602481 := by exact prefixLift 5602481
  have htrace : WordTrace (prefixWord ++ tailWord_5602481) baseStart_5602481 baseEnd_5602481 := by
    simpa [prefixWord, tailWord_5602481, baseEnd_5602481] using wordTrace_append hprefix tailTrace_5602481
  have hstable : (prefixWord ++ tailWord_5602481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602481).length < 2 ^ (prefixWord ++ tailWord_5602481).sum := by decide
  have hdescent : baseEnd_5602481 < baseStart_5602481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602487 : List Nat := [1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 5]
def baseStart_5602487 : Nat := 118140960795 + 5602487 * 2 ^ 59
def prefixEnd_5602487 : Nat := 4983230072969 + 3 ^ 40 * 5602487 * 2
def baseEnd_5602487 : Nat := 2876768691565926977547137

theorem tailTrace_5602487 : CollatzResearch.WordTrace tailWord_5602487 prefixEnd_5602487 2876768691565926977547137 := by
  unfold tailWord_5602487
  simp only [CollatzResearch.WordTrace]
  refine ⟨204339488054153902447693715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136226325369435934965129143 204339488054153902447693715)
  ·
    refine ⟨306509232081230853671540573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204339488054153902447693715 306509232081230853671540573)
    ·
      refine ⟨114940962030461570126827715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306509232081230853671540573 114940962030461570126827715)
      ·
        refine ⟨172411443045692355190241573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114940962030461570126827715 172411443045692355190241573)
        ·
          refine ⟨32327145571067316598170295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172411443045692355190241573 32327145571067316598170295)
          ·
            refine ⟨48490718356600974897255443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32327145571067316598170295 48490718356600974897255443)
            ·
              refine ⟨72736077534901462345883165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48490718356600974897255443 72736077534901462345883165)
              ·
                refine ⟨27276029075588048379706187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72736077534901462345883165 27276029075588048379706187)
                ·
                  refine ⟨40914043613382072569559281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27276029075588048379706187 40914043613382072569559281)
                  ·
                    refine ⟨30685532710036554427169461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40914043613382072569559281 30685532710036554427169461)
                    ·
                      refine ⟨2876768691565926977547137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30685532710036554427169461 2876768691565926977547137)
                      ·
                        rfl

theorem cell23_5602487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_5602487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602487 prefixEnd_5602487 := by exact prefixLift 5602487
  have htrace : WordTrace (prefixWord ++ tailWord_5602487) baseStart_5602487 baseEnd_5602487 := by
    simpa [prefixWord, tailWord_5602487, baseEnd_5602487] using wordTrace_append hprefix tailTrace_5602487
  have hstable : (prefixWord ++ tailWord_5602487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602487).length < 2 ^ (prefixWord ++ tailWord_5602487).sum := by decide
  have hdescent : baseEnd_5602487 < baseStart_5602487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602498 : List Nat := [3, 5, 1, 1, 2, 1, 1, 2, 7]
def baseStart_5602498 : Nat := 118140960795 + 5602498 * 2 ^ 59
def prefixEnd_5602498 : Nat := 4983230072969 + 3 ^ 40 * 5602498 * 2
def baseEnd_5602498 : Nat := 319641593317014048278843

theorem tailTrace_5602498 : CollatzResearch.WordTrace tailWord_5602498 prefixEnd_5602498 319641593317014048278843 := by
  unfold tailWord_5602498
  simp only [CollatzResearch.WordTrace]
  refine ⟨51084972314278512831586037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136226592838076034217562765 51084972314278512831586037)
  ·
    refine ⟨4789216154463610577961191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51084972314278512831586037 4789216154463610577961191)
    ·
      refine ⟨7183824231695415866941787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4789216154463610577961191 7183824231695415866941787)
      ·
        refine ⟨10775736347543123800412681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7183824231695415866941787 10775736347543123800412681)
        ·
          refine ⟨8081802260657342850309511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10775736347543123800412681 8081802260657342850309511)
          ·
            refine ⟨12122703390986014275464267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8081802260657342850309511 12122703390986014275464267)
            ·
              refine ⟨18184055086479021413196401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12122703390986014275464267 18184055086479021413196401)
              ·
                refine ⟨13638041314859266059897301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18184055086479021413196401 13638041314859266059897301)
                ·
                  refine ⟨319641593317014048278843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13638041314859266059897301 319641593317014048278843)
                  ·
                    rfl

theorem cell23_5602498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_5602498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602498 prefixEnd_5602498 := by exact prefixLift 5602498
  have htrace : WordTrace (prefixWord ++ tailWord_5602498) baseStart_5602498 baseEnd_5602498 := by
    simpa [prefixWord, tailWord_5602498, baseEnd_5602498] using wordTrace_append hprefix tailTrace_5602498
  have hstable : (prefixWord ++ tailWord_5602498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602498).length < 2 ^ (prefixWord ++ tailWord_5602498).sum := by decide
  have hdescent : baseEnd_5602498 < baseStart_5602498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602514 : List Nat := [3, 2, 2, 2, 1, 1, 3, 1, 1, 3, 4]
def baseStart_5602514 : Nat := 118140960795 + 5602514 * 2 ^ 59
def prefixEnd_5602514 : Nat := 4983230072969 + 3 ^ 40 * 5602514 * 2
def baseEnd_5602514 : Nat := 2876782555543598371909513

theorem tailTrace_5602514 : CollatzResearch.WordTrace tailWord_5602514 prefixEnd_5602514 2876782555543598371909513 := by
  unfold tailWord_5602514
  simp only [CollatzResearch.WordTrace]
  refine ⟨51085118206264021514731649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136226981883370724039284397 51085118206264021514731649)
  ·
    refine ⟨38313838654698016136048737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51085118206264021514731649 38313838654698016136048737)
    ·
      refine ⟨28735378991023512102036553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38313838654698016136048737 28735378991023512102036553)
      ·
        refine ⟨21551534243267634076527415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28735378991023512102036553 21551534243267634076527415)
        ·
          refine ⟨32327301364901451114791123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21551534243267634076527415 32327301364901451114791123)
          ·
            refine ⟨48490952047352176672186685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32327301364901451114791123 48490952047352176672186685)
            ·
              refine ⟨18184107017757066252070007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48490952047352176672186685 18184107017757066252070007)
              ·
                refine ⟨27276160526635599378105011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18184107017757066252070007 27276160526635599378105011)
                ·
                  refine ⟨40914240789953399067157517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27276160526635599378105011 40914240789953399067157517)
                  ·
                    refine ⟨15342840296232524650184069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40914240789953399067157517 15342840296232524650184069)
                    ·
                      refine ⟨2876782555543598371909513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15342840296232524650184069 2876782555543598371909513)
                      ·
                        rfl

theorem cell23_5602514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_5602514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602514 prefixEnd_5602514 := by exact prefixLift 5602514
  have htrace : WordTrace (prefixWord ++ tailWord_5602514) baseStart_5602514 baseEnd_5602514 := by
    simpa [prefixWord, tailWord_5602514, baseEnd_5602514] using wordTrace_append hprefix tailTrace_5602514
  have hstable : (prefixWord ++ tailWord_5602514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602514).length < 2 ^ (prefixWord ++ tailWord_5602514).sum := by decide
  have hdescent : baseEnd_5602514 < baseStart_5602514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602527 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 6]
def baseStart_5602527 : Nat := 118140960795 + 5602527 * 2 ^ 59
def prefixEnd_5602527 : Nat := 4983230072969 + 3 ^ 40 * 5602527 * 2
def baseEnd_5602527 : Nat := 2876789230792106821046953

theorem tailTrace_5602527 : CollatzResearch.WordTrace tailWord_5602527 prefixEnd_5602527 2876789230792106821046953 := by
  unfold tailWord_5602527
  simp only [CollatzResearch.WordTrace]
  refine ⟨204340946974008989279149835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136227297982672659519433223 204340946974008989279149835)
  ·
    refine ⟨306511420461013483918724753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204340946974008989279149835 306511420461013483918724753)
    ·
      refine ⟨229883565345760112939043565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306511420461013483918724753 229883565345760112939043565)
      ·
        refine ⟨86206337004660042352141337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229883565345760112939043565 86206337004660042352141337)
        ·
          refine ⟨64654752753495031764106003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86206337004660042352141337 64654752753495031764106003)
          ·
            refine ⟨96982129130242547646159005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64654752753495031764106003 96982129130242547646159005)
            ·
              refine ⟨36368298423840955367309627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96982129130242547646159005 36368298423840955367309627)
              ·
                refine ⟨54552447635761433050964441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36368298423840955367309627 54552447635761433050964441)
                ·
                  refine ⟨40914335726821074788223331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54552447635761433050964441 40914335726821074788223331)
                  ·
                    refine ⟨61371503590231612182334997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40914335726821074788223331 61371503590231612182334997)
                    ·
                      refine ⟨2876789230792106821046953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61371503590231612182334997 2876789230792106821046953)
                      ·
                        rfl

theorem cell23_5602527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_5602527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602527 prefixEnd_5602527 := by exact prefixLift 5602527
  have htrace : WordTrace (prefixWord ++ tailWord_5602527) baseStart_5602527 baseEnd_5602527 := by
    simpa [prefixWord, tailWord_5602527, baseEnd_5602527] using wordTrace_append hprefix tailTrace_5602527
  have hstable : (prefixWord ++ tailWord_5602527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602527).length < 2 ^ (prefixWord ++ tailWord_5602527).sum := by decide
  have hdescent : baseEnd_5602527 < baseStart_5602527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602541 : List Nat := [1, 5, 1, 2, 2, 1, 1, 3, 3, 4]
def baseStart_5602541 : Nat := 118140960795 + 5602541 * 2 ^ 59
def prefixEnd_5602541 : Nat := 4983230072969 + 3 ^ 40 * 5602541 * 2
def baseEnd_5602541 : Nat := 958932139840423255423963

theorem tailTrace_5602541 : CollatzResearch.WordTrace tailWord_5602541 prefixEnd_5602541 958932139840423255423963 := by
  unfold tailWord_5602541
  simp only [CollatzResearch.WordTrace]
  refine ⟨204341457595958269670159477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136227638397305513113439651 204341457595958269670159477)
  ·
    refine ⟨19157011649621087781577451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 204341457595958269670159477 19157011649621087781577451)
    ·
      refine ⟨28735517474431631672366177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19157011649621087781577451 28735517474431631672366177)
      ·
        refine ⟨21551638105823723754274633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28735517474431631672366177 21551638105823723754274633)
        ·
          refine ⟨16163728579367792815705975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21551638105823723754274633 16163728579367792815705975)
          ·
            refine ⟨24245592869051689223558963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16163728579367792815705975 24245592869051689223558963)
            ·
              refine ⟨36368389303577533835338445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24245592869051689223558963 36368389303577533835338445)
              ·
                refine ⟨13638145988841575188251917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36368389303577533835338445 13638145988841575188251917)
                ·
                  refine ⟨5114304745815590695594469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13638145988841575188251917 5114304745815590695594469)
                  ·
                    refine ⟨958932139840423255423963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5114304745815590695594469 958932139840423255423963)
                    ·
                      rfl

theorem cell23_5602541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_5602541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602541 prefixEnd_5602541 := by exact prefixLift 5602541
  have htrace : WordTrace (prefixWord ++ tailWord_5602541) baseStart_5602541 baseEnd_5602541 := by
    simpa [prefixWord, tailWord_5602541, baseEnd_5602541] using wordTrace_append hprefix tailTrace_5602541
  have hstable : (prefixWord ++ tailWord_5602541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602541).length < 2 ^ (prefixWord ++ tailWord_5602541).sum := by decide
  have hdescent : baseEnd_5602541 < baseStart_5602541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602604 : List Nat := [2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 4]
def baseStart_5602604 : Nat := 118140960795 + 5602604 * 2 ^ 59
def prefixEnd_5602604 : Nat := 4983230072969 + 3 ^ 40 * 5602604 * 2
def baseEnd_5602604 : Nat := 2876828768802503019784099

theorem tailTrace_5602604 : CollatzResearch.WordTrace tailWord_5602604 prefixEnd_5602604 2876828768802503019784099 := by
  unfold tailWord_5602604
  simp only [CollatzResearch.WordTrace]
  refine ⟨102171877697365015714851433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136229170263153354286468577 102171877697365015714851433)
  ·
    refine ⟨76628908273023761786138575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102171877697365015714851433 76628908273023761786138575)
    ·
      refine ⟨114943362409535642679207863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76628908273023761786138575 114943362409535642679207863)
      ·
        refine ⟨172415043614303464018811795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114943362409535642679207863 172415043614303464018811795)
        ·
          refine ⟨258622565421455196028217693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172415043614303464018811795 258622565421455196028217693)
          ·
            refine ⟨96983462033045698510581635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 258622565421455196028217693 96983462033045698510581635)
            ·
              refine ⟨145475193049568547765872453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96983462033045698510581635 145475193049568547765872453)
              ·
                refine ⟨27276598696794102706101085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145475193049568547765872453 27276598696794102706101085)
                ·
                  refine ⟨10228724511297788514787907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27276598696794102706101085 10228724511297788514787907)
                  ·
                    refine ⟨15343086766946682772181861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10228724511297788514787907 15343086766946682772181861)
                    ·
                      refine ⟨2876828768802503019784099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15343086766946682772181861 2876828768802503019784099)
                      ·
                        rfl

theorem cell23_5602604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_5602604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602604 prefixEnd_5602604 := by exact prefixLift 5602604
  have htrace : WordTrace (prefixWord ++ tailWord_5602604) baseStart_5602604 baseEnd_5602604 := by
    simpa [prefixWord, tailWord_5602604, baseEnd_5602604] using wordTrace_append hprefix tailTrace_5602604
  have hstable : (prefixWord ++ tailWord_5602604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602604).length < 2 ^ (prefixWord ++ tailWord_5602604).sum := by decide
  have hdescent : baseEnd_5602604 < baseStart_5602604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602605 : List Nat := [1, 5, 3, 1, 1, 3, 2, 1, 6]
def baseStart_5602605 : Nat := 118140960795 + 5602605 * 2 ^ 59
def prefixEnd_5602605 : Nat := 4983230072969 + 3 ^ 40 * 5602605 * 2
def baseEnd_5602605 : Nat := 319647698031461946207955

theorem tailTrace_5602605 : CollatzResearch.WordTrace tailWord_5602605 prefixEnd_5602605 319647698031461946207955 := by
  unfold tailWord_5602605
  simp only [CollatzResearch.WordTrace]
  refine ⟨204343791867726408600489269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136229194578484272400326179 204343791867726408600489269)
  ·
    refine ⟨19157230487599350806295869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 204343791867726408600489269 19157230487599350806295869)
    ·
      refine ⟨7183961432849756552360951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19157230487599350806295869 7183961432849756552360951)
      ·
        refine ⟨10775942149274634828541427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7183961432849756552360951 10775942149274634828541427)
        ·
          refine ⟨16163913223911952242812141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10775942149274634828541427 16163913223911952242812141)
          ·
            refine ⟨6061467458966982091054553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16163913223911952242812141 6061467458966982091054553)
            ·
              refine ⟨4546100594225236568290915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6061467458966982091054553 4546100594225236568290915)
              ·
                refine ⟨6819150891337854852436373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4546100594225236568290915 6819150891337854852436373)
                ·
                  refine ⟨319647698031461946207955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6819150891337854852436373 319647698031461946207955)
                  ·
                    rfl

theorem cell23_5602605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_5602605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602605 prefixEnd_5602605 := by exact prefixLift 5602605
  have htrace : WordTrace (prefixWord ++ tailWord_5602605) baseStart_5602605 baseEnd_5602605 := by
    simpa [prefixWord, tailWord_5602605, baseEnd_5602605] using wordTrace_append hprefix tailTrace_5602605
  have hstable : (prefixWord ++ tailWord_5602605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602605).length < 2 ^ (prefixWord ++ tailWord_5602605).sum := by decide
  have hdescent : baseEnd_5602605 < baseStart_5602605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602625 : List Nat := [1, 2, 5, 2, 1, 2, 2, 1, 2, 3, 2]
def baseStart_5602625 : Nat := 118140960795 + 5602625 * 2 ^ 59
def prefixEnd_5602625 : Nat := 4983230072969 + 3 ^ 40 * 5602625 * 2
def baseEnd_5602625 : Nat := 2876839551896247437621503

theorem tailTrace_5602625 : CollatzResearch.WordTrace tailWord_5602625 prefixEnd_5602625 2876839551896247437621503 := by
  unfold tailWord_5602625
  simp only [CollatzResearch.WordTrace]
  refine ⟨204344521327653952016217329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136229680885102634677478219 204344521327653952016217329)
  ·
    refine ⟨153258390995740464012162997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204344521327653952016217329 153258390995740464012162997)
    ·
      refine ⟨14367974155850668501140281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153258390995740464012162997 14367974155850668501140281)
      ·
        refine ⟨10775980616888001375855211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14367974155850668501140281 10775980616888001375855211)
        ·
          refine ⟨16163970925332002063782817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10775980616888001375855211 16163970925332002063782817)
          ·
            refine ⟨12122978193999001547837113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16163970925332002063782817 12122978193999001547837113)
            ·
              refine ⟨9092233645499251160877835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12122978193999001547837113 9092233645499251160877835)
              ·
                refine ⟨13638350468248876741316753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9092233645499251160877835 13638350468248876741316753)
                ·
                  refine ⟨10228762851186657555987565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13638350468248876741316753 10228762851186657555987565)
                  ·
                    refine ⟨3835786069194996583495337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10228762851186657555987565 3835786069194996583495337)
                    ·
                      refine ⟨2876839551896247437621503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3835786069194996583495337 2876839551896247437621503)
                      ·
                        rfl

theorem cell23_5602625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_5602625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602625 prefixEnd_5602625 := by exact prefixLift 5602625
  have htrace : WordTrace (prefixWord ++ tailWord_5602625) baseStart_5602625 baseEnd_5602625 := by
    simpa [prefixWord, tailWord_5602625, baseEnd_5602625] using wordTrace_append hprefix tailTrace_5602625
  have hstable : (prefixWord ++ tailWord_5602625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602625).length < 2 ^ (prefixWord ++ tailWord_5602625).sum := by decide
  have hdescent : baseEnd_5602625 < baseStart_5602625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602638 : List Nat := [4, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4]
def baseStart_5602638 : Nat := 118140960795 + 5602638 * 2 ^ 59
def prefixEnd_5602638 : Nat := 4983230072969 + 3 ^ 40 * 5602638 * 2
def baseEnd_5602638 : Nat := 2876846227144755886758943

theorem tailTrace_5602638 : CollatzResearch.WordTrace tailWord_5602638 prefixEnd_5602638 2876846227144755886758943 := by
  unfold tailWord_5602638
  simp only [CollatzResearch.WordTrace]
  refine ⟨25543124434575856904555071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136229996984404570157627045 25543124434575856904555071)
  ·
    refine ⟨38314686651863785356832607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25543124434575856904555071 38314686651863785356832607)
    ·
      refine ⟨57472029977795678035248911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38314686651863785356832607 57472029977795678035248911)
      ·
        refine ⟨86208044966693517052873367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57472029977795678035248911 86208044966693517052873367)
        ·
          refine ⟨129312067450040275579310051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86208044966693517052873367 129312067450040275579310051)
          ·
            refine ⟨193968101175060413368965077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129312067450040275579310051 193968101175060413368965077)
            ·
              refine ⟨4546127371290478438335119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 193968101175060413368965077 4546127371290478438335119)
              ·
                refine ⟨6819191056935717657502679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4546127371290478438335119 6819191056935717657502679)
                ·
                  refine ⟨10228786585403576486254019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6819191056935717657502679 10228786585403576486254019)
                  ·
                    refine ⟨15343179878105364729381029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10228786585403576486254019 15343179878105364729381029)
                    ·
                      refine ⟨2876846227144755886758943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15343179878105364729381029 2876846227144755886758943)
                      ·
                        rfl

theorem cell23_5602638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4].length) (baseStart_5602638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602638 prefixEnd_5602638 := by exact prefixLift 5602638
  have htrace : WordTrace (prefixWord ++ tailWord_5602638) baseStart_5602638 baseEnd_5602638 := by
    simpa [prefixWord, tailWord_5602638, baseEnd_5602638] using wordTrace_append hprefix tailTrace_5602638
  have hstable : (prefixWord ++ tailWord_5602638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602638).length < 2 ^ (prefixWord ++ tailWord_5602638).sum := by decide
  have hdescent : baseEnd_5602638 < baseStart_5602638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602671 : List Nat := [1, 1, 2, 1, 3, 1, 6, 1, 1, 3, 3]
def baseStart_5602671 : Nat := 118140960795 + 5602671 * 2 ^ 59
def prefixEnd_5602671 : Nat := 4983230072969 + 3 ^ 40 * 5602671 * 2
def baseEnd_5602671 : Nat := 2876863172006354257646291

theorem tailTrace_5602671 : CollatzResearch.WordTrace tailWord_5602671 prefixEnd_5602671 2876863172006354257646291 := by
  unfold tailWord_5602671
  simp only [CollatzResearch.WordTrace]
  refine ⟨204346199085487301872391867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136230799390324867914927911 204346199085487301872391867)
  ·
    refine ⟨306519298628230952808587801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204346199085487301872391867 306519298628230952808587801)
    ·
      refine ⟨229889473971173214606440851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306519298628230952808587801 229889473971173214606440851)
      ·
        refine ⟨344834210956759821909661277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229889473971173214606440851 344834210956759821909661277)
        ·
          refine ⟨129312829108784933216122979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 344834210956759821909661277 129312829108784933216122979)
          ·
            refine ⟨193969243663177399824184469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129312829108784933216122979 193969243663177399824184469)
            ·
              refine ⟨9092308296711440616758647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 193969243663177399824184469 9092308296711440616758647)
              ·
                refine ⟨13638462445067160925137971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9092308296711440616758647 13638462445067160925137971)
                ·
                  refine ⟨20457693667600741387706957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13638462445067160925137971 20457693667600741387706957)
                  ·
                    refine ⟨7671635125350278020390109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20457693667600741387706957 7671635125350278020390109)
                    ·
                      refine ⟨2876863172006354257646291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7671635125350278020390109 2876863172006354257646291)
                      ·
                        rfl

theorem cell23_5602671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 3, 3].length) (baseStart_5602671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602671 prefixEnd_5602671 := by exact prefixLift 5602671
  have htrace : WordTrace (prefixWord ++ tailWord_5602671) baseStart_5602671 baseEnd_5602671 := by
    simpa [prefixWord, tailWord_5602671, baseEnd_5602671] using wordTrace_append hprefix tailTrace_5602671
  have hstable : (prefixWord ++ tailWord_5602671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602671).length < 2 ^ (prefixWord ++ tailWord_5602671).sum := by decide
  have hdescent : baseEnd_5602671 < baseStart_5602671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602674 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 2, 7]
def baseStart_5602674 : Nat := 118140960795 + 5602674 * 2 ^ 59
def prefixEnd_5602674 : Nat := 4983230072969 + 3 ^ 40 * 5602674 * 2
def baseEnd_5602674 : Nat := 958954904149439248636259

theorem tailTrace_5602674 : CollatzResearch.WordTrace tailWord_5602674 prefixEnd_5602674 958954904149439248636259 := by
  unfold tailWord_5602674
  simp only [CollatzResearch.WordTrace]
  refine ⟨51086577126119108346187769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136230872336317622256500717 51086577126119108346187769)
  ·
    refine ⟨38314932844589331259640827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51086577126119108346187769 38314932844589331259640827)
    ·
      refine ⟨57472399266883996889461241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38314932844589331259640827 57472399266883996889461241)
      ·
        refine ⟨43104299450162997667095931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57472399266883996889461241 43104299450162997667095931)
        ·
          refine ⟨64656449175244496500643897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43104299450162997667095931 64656449175244496500643897)
          ·
            refine ⟨48492336881433372375482923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64656449175244496500643897 48492336881433372375482923)
            ·
              refine ⟨72738505322150058563224385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48492336881433372375482923 72738505322150058563224385)
              ·
                refine ⟨54553878991612543922418289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72738505322150058563224385 54553878991612543922418289)
                ·
                  refine ⟨40915409243709407941813717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54553878991612543922418289 40915409243709407941813717)
                  ·
                    refine ⟨958954904149439248636259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40915409243709407941813717 958954904149439248636259)
                    ·
                      rfl

theorem cell23_5602674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_5602674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602674 prefixEnd_5602674 := by exact prefixLift 5602674
  have htrace : WordTrace (prefixWord ++ tailWord_5602674) baseStart_5602674 baseEnd_5602674 := by
    simpa [prefixWord, tailWord_5602674, baseEnd_5602674] using wordTrace_append hprefix tailTrace_5602674
  have hstable : (prefixWord ++ tailWord_5602674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602674).length < 2 ^ (prefixWord ++ tailWord_5602674).sum := by decide
  have hdescent : baseEnd_5602674 < baseStart_5602674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602684 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 2, 2, 5]
def baseStart_5602684 : Nat := 118140960795 + 5602684 * 2 ^ 59
def prefixEnd_5602684 : Nat := 4983230072969 + 3 ^ 40 * 5602684 * 2
def baseEnd_5602684 : Nat := 2876869847254862706783731

theorem tailTrace_5602684 : CollatzResearch.WordTrace tailWord_5602684 prefixEnd_5602684 2876869847254862706783731 := by
  unfold tailWord_5602684
  simp only [CollatzResearch.WordTrace]
  refine ⟨102173336617220102546307553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136231115489626803395076737 102173336617220102546307553)
  ·
    refine ⟨76630002462915076909730665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102173336617220102546307553 76630002462915076909730665)
    ·
      refine ⟨57472501847186307682297999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76630002462915076909730665 57472501847186307682297999)
      ·
        refine ⟨86208752770779461523446999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57472501847186307682297999 86208752770779461523446999)
        ·
          refine ⟨129313129156169192285170499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86208752770779461523446999 129313129156169192285170499)
          ·
            refine ⟨193969693734253788427755749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129313129156169192285170499 193969693734253788427755749)
            ·
              refine ⟨36369317575172585330204203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 193969693734253788427755749 36369317575172585330204203)
              ·
                refine ⟨54553976362758877995306305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36369317575172585330204203 54553976362758877995306305)
                ·
                  refine ⟨40915482272069158496479729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54553976362758877995306305 40915482272069158496479729)
                  ·
                    refine ⟨30686611704051868872359797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40915482272069158496479729 30686611704051868872359797)
                    ·
                      refine ⟨2876869847254862706783731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30686611704051868872359797 2876869847254862706783731)
                      ·
                        rfl

theorem cell23_5602684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_5602684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602684 prefixEnd_5602684 := by exact prefixLift 5602684
  have htrace : WordTrace (prefixWord ++ tailWord_5602684) baseStart_5602684 baseEnd_5602684 := by
    simpa [prefixWord, tailWord_5602684, baseEnd_5602684] using wordTrace_append hprefix tailTrace_5602684
  have hstable : (prefixWord ++ tailWord_5602684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602684).length < 2 ^ (prefixWord ++ tailWord_5602684).sum := by decide
  have hdescent : baseEnd_5602684 < baseStart_5602684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602689 : List Nat := [1, 2, 4, 3, 2, 1, 2, 3, 1, 2, 2]
def baseStart_5602689 : Nat := 118140960795 + 5602689 * 2 ^ 59
def prefixEnd_5602689 : Nat := 4983230072969 + 3 ^ 40 * 5602689 * 2
def baseEnd_5602689 : Nat := 2876872414658135187221209

theorem tailTrace_5602689 : CollatzResearch.WordTrace tailWord_5602689 prefixEnd_5602689 2876872414658135187221209 := by
  unfold tailWord_5602689
  simp only [CollatzResearch.WordTrace]
  refine ⟨204346855599422090946547121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136231237066281393964364747 204346855599422090946547121)
  ·
    refine ⟨153260141699566568209910341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204346855599422090946547121 153260141699566568209910341)
    ·
      refine ⟨28736276568668731539358189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153260141699566568209910341 28736276568668731539358189)
      ·
        refine ⟨10776103713250774327259321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28736276568668731539358189 10776103713250774327259321)
        ·
          refine ⟨8082077784938080745444491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10776103713250774327259321 8082077784938080745444491)
          ·
            refine ⟨12123116677407121118166737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8082077784938080745444491 12123116677407121118166737)
            ·
              refine ⟨9092337508055340838625053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12123116677407121118166737 9092337508055340838625053)
              ·
                refine ⟨3409626565520752814484395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9092337508055340838625053 3409626565520752814484395)
                ·
                  refine ⟨5114439848281129221726593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3409626565520752814484395 5114439848281129221726593)
                  ·
                    refine ⟨3835829886210846916294945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5114439848281129221726593 3835829886210846916294945)
                    ·
                      refine ⟨2876872414658135187221209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3835829886210846916294945 2876872414658135187221209)
                      ·
                        rfl

theorem cell23_5602689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_5602689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602689 prefixEnd_5602689 := by exact prefixLift 5602689
  have htrace : WordTrace (prefixWord ++ tailWord_5602689) baseStart_5602689 baseEnd_5602689 := by
    simpa [prefixWord, tailWord_5602689, baseEnd_5602689] using wordTrace_append hprefix tailTrace_5602689
  have hstable : (prefixWord ++ tailWord_5602689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602689).length < 2 ^ (prefixWord ++ tailWord_5602689).sum := by decide
  have hdescent : baseEnd_5602689 < baseStart_5602689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602722 : List Nat := [3, 3, 1, 2, 1, 3, 3, 1, 2, 1, 3]
def baseStart_5602722 : Nat := 118140960795 + 5602722 * 2 ^ 59
def prefixEnd_5602722 : Nat := 4983230072969 + 3 ^ 40 * 5602722 * 2
def baseEnd_5602722 : Nat := 2876889359519733558108557

theorem tailTrace_5602722 : CollatzResearch.WordTrace tailWord_5602722 prefixEnd_5602722 2876889359519733558108557 := by
  unfold tailWord_5602722
  simp only [CollatzResearch.WordTrace]
  refine ⟨51087014802075634395624605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136232039472201691721665613 51087014802075634395624605)
  ·
    refine ⟨19157630550778362898359227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51087014802075634395624605 19157630550778362898359227)
    ·
      refine ⟨28736445826167544347538841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19157630550778362898359227 28736445826167544347538841)
      ·
        refine ⟨21552334369625658260654131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28736445826167544347538841 21552334369625658260654131)
        ·
          refine ⟨32328501554438487390981197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21552334369625658260654131 32328501554438487390981197)
          ·
            refine ⟨12123188082914432771617949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32328501554438487390981197 12123188082914432771617949)
            ·
              refine ⟨4546195531092912289356731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12123188082914432771617949 4546195531092912289356731)
              ·
                refine ⟨6819293296639368434035097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4546195531092912289356731 6819293296639368434035097)
                ·
                  refine ⟨5114469972479526325526323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6819293296639368434035097 5114469972479526325526323)
                  ·
                    refine ⟨7671704958719289488289485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5114469972479526325526323 7671704958719289488289485)
                    ·
                      refine ⟨2876889359519733558108557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7671704958719289488289485 2876889359519733558108557)
                      ·
                        rfl

theorem cell23_5602722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_5602722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602722 prefixEnd_5602722 := by exact prefixLift 5602722
  have htrace : WordTrace (prefixWord ++ tailWord_5602722) baseStart_5602722 baseEnd_5602722 := by
    simpa [prefixWord, tailWord_5602722, baseEnd_5602722] using wordTrace_append hprefix tailTrace_5602722
  have hstable : (prefixWord ++ tailWord_5602722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602722).length < 2 ^ (prefixWord ++ tailWord_5602722).sum := by decide
  have hdescent : baseEnd_5602722 < baseStart_5602722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602748 : List Nat := [2, 2, 2, 4, 2, 1, 1, 1, 2, 1, 5]
def baseStart_5602748 : Nat := 118140960795 + 5602748 * 2 ^ 59
def prefixEnd_5602748 : Nat := 4983230072969 + 3 ^ 40 * 5602748 * 2
def baseEnd_5602748 : Nat := 2876902710016750456383437

theorem tailTrace_5602748 : CollatzResearch.WordTrace tailWord_5602748 prefixEnd_5602748 2876902710016750456383437 := by
  unfold tailWord_5602748
  simp only [CollatzResearch.WordTrace]
  refine ⟨102174503753104172011472449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136232671670805562681963265 102174503753104172011472449)
  ·
    refine ⟨76630877814828129008604337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102174503753104172011472449 76630877814828129008604337)
    ·
      refine ⟨57473158361121096756453253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76630877814828129008604337 57473158361121096756453253)
      ·
        refine ⟨10776217192710205641834985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57473158361121096756453253 10776217192710205641834985)
        ·
          refine ⟨8082162894532654231376239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10776217192710205641834985 8082162894532654231376239)
          ·
            refine ⟨12123244341798981347064359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8082162894532654231376239 12123244341798981347064359)
            ·
              refine ⟨18184866512698472020596539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12123244341798981347064359 18184866512698472020596539)
              ·
                refine ⟨27277299769047708030894809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18184866512698472020596539 27277299769047708030894809)
                ·
                  refine ⟨20457974826785781023171107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27277299769047708030894809 20457974826785781023171107)
                  ·
                    refine ⟨30686962240178671534756661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20457974826785781023171107 30686962240178671534756661)
                    ·
                      refine ⟨2876902710016750456383437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30686962240178671534756661 2876902710016750456383437)
                      ·
                        rfl

theorem cell23_5602748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_5602748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602748 prefixEnd_5602748 := by exact prefixLift 5602748
  have htrace : WordTrace (prefixWord ++ tailWord_5602748) baseStart_5602748 baseEnd_5602748 := by
    simpa [prefixWord, tailWord_5602748, baseEnd_5602748] using wordTrace_append hprefix tailTrace_5602748
  have hstable : (prefixWord ++ tailWord_5602748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602748).length < 2 ^ (prefixWord ++ tailWord_5602748).sum := by decide
  have hdescent : baseEnd_5602748 < baseStart_5602748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602798 : List Nat := [4, 1, 2, 1, 2, 1, 4, 1, 2, 5]
def baseStart_5602798 : Nat := 118140960795 + 5602798 * 2 ^ 59
def prefixEnd_5602798 : Nat := 4983230072969 + 3 ^ 40 * 5602798 * 2
def baseEnd_5602798 : Nat := 958976128016491753586069

theorem tailTrace_5602798 : CollatzResearch.WordTrace tailWord_5602798 prefixEnd_5602798 958976128016491753586069 := by
  unfold tailWord_5602798
  simp only [CollatzResearch.WordTrace]
  refine ⟨25543853894503400320283131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136233887437351468374843365 25543853894503400320283131)
  ·
    refine ⟨38315780841755100480424697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25543853894503400320283131 38315780841755100480424697)
    ·
      refine ⟨28736835631316325360318523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38315780841755100480424697 28736835631316325360318523)
      ·
        refine ⟨43105253446974488040477785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28736835631316325360318523 43105253446974488040477785)
        ·
          refine ⟨32328940085230866030358339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43105253446974488040477785 32328940085230866030358339)
          ·
            refine ⟨48493410127846299045537509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32328940085230866030358339 48493410127846299045537509)
            ·
              refine ⟨9092514398971181071038283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48493410127846299045537509 9092514398971181071038283)
              ·
                refine ⟨13638771598456771606557425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9092514398971181071038283 13638771598456771606557425)
                ·
                  refine ⟨10229078698842578704918069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13638771598456771606557425 10229078698842578704918069)
                  ·
                    refine ⟨958976128016491753586069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10229078698842578704918069 958976128016491753586069)
                    ·
                      rfl

theorem cell23_5602798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_5602798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602798 prefixEnd_5602798 := by exact prefixLift 5602798
  have htrace : WordTrace (prefixWord ++ tailWord_5602798) baseStart_5602798 baseEnd_5602798 := by
    simpa [prefixWord, tailWord_5602798, baseEnd_5602798] using wordTrace_append hprefix tailTrace_5602798
  have hstable : (prefixWord ++ tailWord_5602798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602798).length < 2 ^ (prefixWord ++ tailWord_5602798).sum := by decide
  have hdescent : baseEnd_5602798 < baseStart_5602798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602811 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 5, 4]
def baseStart_5602811 : Nat := 118140960795 + 5602811 * 2 ^ 59
def prefixEnd_5602811 : Nat := 4983230072969 + 3 ^ 40 * 5602811 * 2
def baseEnd_5602811 : Nat := 958978353099327903298549

theorem tailTrace_5602811 : CollatzResearch.WordTrace tailWord_5602811 prefixEnd_5602811 958978353099327903298549 := by
  unfold tailWord_5602811
  simp only [CollatzResearch.WordTrace]
  refine ⟨204351305304980105782488287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136234203536653403854992191 204351305304980105782488287)
  ·
    refine ⟨306526957957470158673732431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204351305304980105782488287 306526957957470158673732431)
    ·
      refine ⟨459790436936205238010598647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306526957957470158673732431 459790436936205238010598647)
      ·
        refine ⟨689685655404307857015897971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459790436936205238010598647 689685655404307857015897971)
        ·
          refine ⟨1034528483106461785523846957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 689685655404307857015897971 1034528483106461785523846957)
          ·
            refine ⟨387948181164923169571442609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1034528483106461785523846957 387948181164923169571442609)
            ·
              refine ⟨290961135873692377178581957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 387948181164923169571442609 290961135873692377178581957)
              ·
                refine ⟨54555212976317320720984117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 290961135873692377178581957 54555212976317320720984117)
                ·
                  refine ⟨5114551216529748817592261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54555212976317320720984117 5114551216529748817592261)
                  ·
                    refine ⟨958978353099327903298549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5114551216529748817592261 958978353099327903298549)
                    ·
                      rfl

theorem cell23_5602811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 5, 4].length) (baseStart_5602811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602811 prefixEnd_5602811 := by exact prefixLift 5602811
  have htrace : WordTrace (prefixWord ++ tailWord_5602811) baseStart_5602811 baseEnd_5602811 := by
    simpa [prefixWord, tailWord_5602811, baseEnd_5602811] using wordTrace_append hprefix tailTrace_5602811
  have hstable : (prefixWord ++ tailWord_5602811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602811).length < 2 ^ (prefixWord ++ tailWord_5602811).sum := by decide
  have hdescent : baseEnd_5602811 < baseStart_5602811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602821 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 3, 4, 3]
def baseStart_5602821 : Nat := 118140960795 + 5602821 * 2 ^ 59
def prefixEnd_5602821 : Nat := 4983230072969 + 3 ^ 40 * 5602821 * 2
def baseEnd_5602821 : Nat := 2876940194104528670770601

theorem tailTrace_5602821 : CollatzResearch.WordTrace tailWord_5602821 prefixEnd_5602821 2876940194104528670770601 := by
  unfold tailWord_5602821
  simp only [CollatzResearch.WordTrace]
  refine ⟨204351670034943877490352317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136234446689962584993568211 204351670034943877490352317)
  ·
    refine ⟨76631876263103954058882119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204351670034943877490352317 76631876263103954058882119)
    ·
      refine ⟨114947814394655931088323179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76631876263103954058882119 114947814394655931088323179)
      ·
        refine ⟨172421721591983896632484769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114947814394655931088323179 172421721591983896632484769)
        ·
          refine ⟨129316291193987922474363577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172421721591983896632484769 129316291193987922474363577)
          ·
            refine ⟨96987218395490941855772683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129316291193987922474363577 96987218395490941855772683)
            ·
              refine ⟨145480827593236412783659025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96987218395490941855772683 145480827593236412783659025)
              ·
                refine ⟨109110620694927309587744269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145480827593236412783659025 109110620694927309587744269)
                ·
                  refine ⟨40916482760597741095404101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109110620694927309587744269 40916482760597741095404101)
                  ·
                    refine ⟨7671840517612076455388269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40916482760597741095404101 7671840517612076455388269)
                    ·
                      refine ⟨2876940194104528670770601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7671840517612076455388269 2876940194104528670770601)
                      ·
                        rfl

theorem cell23_5602821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 4, 3].length) (baseStart_5602821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602821 prefixEnd_5602821 := by exact prefixLift 5602821
  have htrace : WordTrace (prefixWord ++ tailWord_5602821) baseStart_5602821 baseEnd_5602821 := by
    simpa [prefixWord, tailWord_5602821, baseEnd_5602821] using wordTrace_append hprefix tailTrace_5602821
  have hstable : (prefixWord ++ tailWord_5602821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602821).length < 2 ^ (prefixWord ++ tailWord_5602821).sum := by decide
  have hdescent : baseEnd_5602821 < baseStart_5602821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602862 : List Nat := [4, 1, 3, 1, 2, 1, 1, 5, 1, 4]
def baseStart_5602862 : Nat := 118140960795 + 5602862 * 2 ^ 59
def prefixEnd_5602862 : Nat := 4983230072969 + 3 ^ 40 * 5602862 * 2
def baseEnd_5602862 : Nat := 958987082270454336785971

theorem tailTrace_5602862 : CollatzResearch.WordTrace tailWord_5602862 prefixEnd_5602862 958987082270454336785971 := by
  unfold tailWord_5602862
  simp only [CollatzResearch.WordTrace]
  refine ⟨25544145678474417686574355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136235443618530227661729893 25544145678474417686574355)
  ·
    refine ⟨38316218517711626529861533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25544145678474417686574355 38316218517711626529861533)
    ·
      refine ⟨14368581944141859948698075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38316218517711626529861533 14368581944141859948698075)
      ·
        refine ⟨21552872916212789923047113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14368581944141859948698075 21552872916212789923047113)
        ·
          refine ⟨16164654687159592442285335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21552872916212789923047113 16164654687159592442285335)
          ·
            refine ⟨24246982030739388663428003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16164654687159592442285335 24246982030739388663428003)
            ·
              refine ⟨36370473046109082995142005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24246982030739388663428003 36370473046109082995142005)
              ·
                refine ⟨3409731848072726530794563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36370473046109082995142005 3409731848072726530794563)
                ·
                  refine ⟨5114597772109089796191845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3409731848072726530794563 5114597772109089796191845)
                  ·
                    refine ⟨958987082270454336785971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5114597772109089796191845 958987082270454336785971)
                    ·
                      rfl

theorem cell23_5602862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_5602862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602862 prefixEnd_5602862 := by exact prefixLift 5602862
  have htrace : WordTrace (prefixWord ++ tailWord_5602862) baseStart_5602862 baseEnd_5602862 := by
    simpa [prefixWord, tailWord_5602862, baseEnd_5602862] using wordTrace_append hprefix tailTrace_5602862
  have hstable : (prefixWord ++ tailWord_5602862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602862).length < 2 ^ (prefixWord ++ tailWord_5602862).sum := by decide
  have hdescent : baseEnd_5602862 < baseStart_5602862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602885 : List Nat := [1, 3, 1, 1, 1, 4, 4, 1, 3, 1, 3]
def baseStart_5602885 : Nat := 118140960795 + 5602885 * 2 ^ 59
def prefixEnd_5602885 : Nat := 4983230072969 + 3 ^ 40 * 5602885 * 2
def baseEnd_5602885 : Nat := 2876973056866416420370307

theorem tailTrace_5602885 : CollatzResearch.WordTrace tailWord_5602885 prefixEnd_5602885 2876973056866416420370307 := by
  unfold tailWord_5602885
  simp only [CollatzResearch.WordTrace]
  refine ⟨204354004306712016420682109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136236002871141344280454739 204354004306712016420682109)
  ·
    refine ⟨76632751615017006157755791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204354004306712016420682109 76632751615017006157755791)
    ·
      refine ⟨114949127422525509236633687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76632751615017006157755791 114949127422525509236633687)
      ·
        refine ⟨172423691133788263854950531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114949127422525509236633687 172423691133788263854950531)
        ·
          refine ⟨258635536700682395782425797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172423691133788263854950531 258635536700682395782425797)
          ·
            refine ⟨48494163131377949209204837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 258635536700682395782425797 48494163131377949209204837)
            ·
              refine ⟨9092655587133365476725907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48494163131377949209204837 9092655587133365476725907)
              ·
                refine ⟨13638983380700048215088861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9092655587133365476725907 13638983380700048215088861)
                ·
                  refine ⟨5114618767762518080658323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13638983380700048215088861 5114618767762518080658323)
                  ·
                    refine ⟨7671928151643777120987485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5114618767762518080658323 7671928151643777120987485)
                    ·
                      refine ⟨2876973056866416420370307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7671928151643777120987485 2876973056866416420370307)
                      ·
                        rfl

theorem cell23_5602885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 3, 1, 3].length) (baseStart_5602885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602885 prefixEnd_5602885 := by exact prefixLift 5602885
  have htrace : WordTrace (prefixWord ++ tailWord_5602885) baseStart_5602885 baseEnd_5602885 := by
    simpa [prefixWord, tailWord_5602885, baseEnd_5602885] using wordTrace_append hprefix tailTrace_5602885
  have hstable : (prefixWord ++ tailWord_5602885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602885).length < 2 ^ (prefixWord ++ tailWord_5602885).sum := by decide
  have hdescent : baseEnd_5602885 < baseStart_5602885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602928 : List Nat := [2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 5]
def baseStart_5602928 : Nat := 118140960795 + 5602928 * 2 ^ 59
def prefixEnd_5602928 : Nat := 4983230072969 + 3 ^ 40 * 5602928 * 2
def baseEnd_5602928 : Nat := 2876995136534559752132609

theorem tailTrace_5602928 : CollatzResearch.WordTrace tailWord_5602928 prefixEnd_5602928 2876995136534559752132609 := by
  unfold tailWord_5602928
  simp only [CollatzResearch.WordTrace]
  refine ⟨102177786322778117382248719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136237048430370823176331625 102177786322778117382248719)
  ·
    refine ⟨153266679484167176073373079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102177786322778117382248719 153266679484167176073373079)
    ·
      refine ⟨229900019226250764110059619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153266679484167176073373079 229900019226250764110059619)
      ·
        refine ⟨344850028839376146165089429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229900019226250764110059619 344850028839376146165089429)
        ·
          refine ⟨16164845101845756851488567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 344850028839376146165089429 16164845101845756851488567)
          ·
            refine ⟨24247267652768635277232851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16164845101845756851488567 24247267652768635277232851)
            ·
              refine ⟨36370901479152952915849277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24247267652768635277232851 36370901479152952915849277)
              ·
                refine ⟨13639088054682357343443479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36370901479152952915849277 13639088054682357343443479)
                ·
                  refine ⟨20458632082023536015165219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13639088054682357343443479 20458632082023536015165219)
                  ·
                    refine ⟨30687948123035304022747829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20458632082023536015165219 30687948123035304022747829)
                    ·
                      refine ⟨2876995136534559752132609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30687948123035304022747829 2876995136534559752132609)
                      ·
                        rfl

theorem cell23_5602928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 5].length) (baseStart_5602928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602928 prefixEnd_5602928 := by exact prefixLift 5602928
  have htrace : WordTrace (prefixWord ++ tailWord_5602928) baseStart_5602928 baseEnd_5602928 := by
    simpa [prefixWord, tailWord_5602928, baseEnd_5602928] using wordTrace_append hprefix tailTrace_5602928
  have hstable : (prefixWord ++ tailWord_5602928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602928).length < 2 ^ (prefixWord ++ tailWord_5602928).sum := by decide
  have hdescent : baseEnd_5602928 < baseStart_5602928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602961 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 4, 7]
def baseStart_5602961 : Nat := 118140960795 + 5602961 * 2 ^ 59
def prefixEnd_5602961 : Nat := 4983230072969 + 3 ^ 40 * 5602961 * 2
def baseEnd_5602961 : Nat := 959004027132052707673319

theorem tailTrace_5602961 : CollatzResearch.WordTrace tailWord_5602961 prefixEnd_5602961 959004027132052707673319 := by
  unfold tailWord_5602961
  simp only [CollatzResearch.WordTrace]
  refine ⟨204356776254436681400448737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136237850836291120933632491 204356776254436681400448737)
  ·
    refine ⟨153267582190827511050336553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204356776254436681400448737 153267582190827511050336553)
    ·
      refine ⟨114950686643120633287752415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153267582190827511050336553 114950686643120633287752415)
      ·
        refine ⟨172426029964680949931628623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114950686643120633287752415 172426029964680949931628623)
        ·
          refine ⟨258639044947021424897442935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172426029964680949931628623 258639044947021424897442935)
          ·
            refine ⟨387958567420532137346164403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258639044947021424897442935 387958567420532137346164403)
            ·
              refine ⟨581937851130798206019246605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387958567420532137346164403 581937851130798206019246605)
              ·
                refine ⟨218226694174049327257217477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 581937851130798206019246605 218226694174049327257217477)
                ·
                  refine ⟨40917505157634248860728277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 218226694174049327257217477 40917505157634248860728277)
                  ·
                    refine ⟨959004027132052707673319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40917505157634248860728277 959004027132052707673319)
                    ·
                      rfl

theorem cell23_5602961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 7].length) (baseStart_5602961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602961 prefixEnd_5602961 := by exact prefixLift 5602961
  have htrace : WordTrace (prefixWord ++ tailWord_5602961) baseStart_5602961 baseEnd_5602961 := by
    simpa [prefixWord, tailWord_5602961, baseEnd_5602961] using wordTrace_append hprefix tailTrace_5602961
  have hstable : (prefixWord ++ tailWord_5602961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602961).length < 2 ^ (prefixWord ++ tailWord_5602961).sum := by decide
  have hdescent : baseEnd_5602961 < baseStart_5602961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5602962 : List Nat := [3, 2, 3, 1, 3, 1, 1, 1, 3, 2, 3]
def baseStart_5602962 : Nat := 118140960795 + 5602962 * 2 ^ 59
def prefixEnd_5602962 : Nat := 4983230072969 + 3 ^ 40 * 5602962 * 2
def baseEnd_5602962 : Nat := 2877012594876812619107453

theorem tailTrace_5602962 : CollatzResearch.WordTrace tailWord_5602962 prefixEnd_5602962 2877012594876812619107453 := by
  unfold tailWord_5602962
  simp only [CollatzResearch.WordTrace]
  refine ⟨51089203181858264642808785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136237875151622039047490093 51089203181858264642808785)
  ·
    refine ⟨38316902386393698482106589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51089203181858264642808785 38316902386393698482106589)
    ·
      refine ⟨14368838394897636930789971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38316902386393698482106589 14368838394897636930789971)
      ·
        refine ⟨21553257592346455396184957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14368838394897636930789971 21553257592346455396184957)
        ·
          refine ⟨8082471597129920773569359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21553257592346455396184957 8082471597129920773569359)
          ·
            refine ⟨12123707395694881160354039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8082471597129920773569359 12123707395694881160354039)
            ·
              refine ⟨18185561093542321740531059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12123707395694881160354039 18185561093542321740531059)
              ·
                refine ⟨27278341640313482610796589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18185561093542321740531059 27278341640313482610796589)
                ·
                  refine ⟨10229378115117555979048721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27278341640313482610796589 10229378115117555979048721)
                  ·
                    refine ⟨7672033586338166984286541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10229378115117555979048721 7672033586338166984286541)
                    ·
                      refine ⟨2877012594876812619107453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7672033586338166984286541 2877012594876812619107453)
                      ·
                        rfl

theorem cell23_5602962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_5602962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5602962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5602962 prefixEnd_5602962 := by exact prefixLift 5602962
  have htrace : WordTrace (prefixWord ++ tailWord_5602962) baseStart_5602962 baseEnd_5602962 := by
    simpa [prefixWord, tailWord_5602962, baseEnd_5602962] using wordTrace_append hprefix tailTrace_5602962
  have hstable : (prefixWord ++ tailWord_5602962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5602962).length < 2 ^ (prefixWord ++ tailWord_5602962).sum := by decide
  have hdescent : baseEnd_5602962 < baseStart_5602962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5602962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603008 : List Nat := [2, 1, 1, 2, 4, 1, 3, 1, 2, 6]
def baseStart_5603008 : Nat := 118140960795 + 5603008 * 2 ^ 59
def prefixEnd_5603008 : Nat := 4983230072969 + 3 ^ 40 * 5603008 * 2
def baseEnd_5603008 : Nat := 959012071662306479710747

theorem tailTrace_5603008 : CollatzResearch.WordTrace tailWord_5603008 prefixEnd_5603008 959012071662306479710747 := by
  unfold tailWord_5603008
  simp only [CollatzResearch.WordTrace]
  refine ⟨102179245242633204213704839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136238993656844272284939785 102179245242633204213704839)
  ·
    refine ⟨153268867863949806320557259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102179245242633204213704839 153268867863949806320557259)
    ·
      refine ⟨229903301795924709480835889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153268867863949806320557259 229903301795924709480835889)
      ·
        refine ⟨172427476346943532110626917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229903301795924709480835889 172427476346943532110626917)
        ·
          refine ⟨32330151815051912270742547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172427476346943532110626917 32330151815051912270742547)
          ·
            refine ⟨48495227722577868406113821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32330151815051912270742547 48495227722577868406113821)
            ·
              refine ⟨18185710395966700652292683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48495227722577868406113821 18185710395966700652292683)
              ·
                refine ⟨27278565593950050978439025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18185710395966700652292683 27278565593950050978439025)
                ·
                  refine ⟨20458924195462538233829269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27278565593950050978439025 20458924195462538233829269)
                  ·
                    refine ⟨959012071662306479710747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20458924195462538233829269 959012071662306479710747)
                    ·
                      rfl

theorem cell23_5603008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 2, 6].length) (baseStart_5603008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603008 prefixEnd_5603008 := by exact prefixLift 5603008
  have htrace : WordTrace (prefixWord ++ tailWord_5603008) baseStart_5603008 baseEnd_5603008 := by
    simpa [prefixWord, tailWord_5603008, baseEnd_5603008] using wordTrace_append hprefix tailTrace_5603008
  have hstable : (prefixWord ++ tailWord_5603008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603008).length < 2 ^ (prefixWord ++ tailWord_5603008).sum := by decide
  have hdescent : baseEnd_5603008 < baseStart_5603008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603030 : List Nat := [5, 2, 1, 3, 2, 1, 2, 1, 1, 2, 3]
def baseStart_5603030 : Nat := 118140960795 + 5603030 * 2 ^ 59
def prefixEnd_5603030 : Nat := 4983230072969 + 3 ^ 40 * 5603030 * 2
def baseEnd_5603030 : Nat := 2877047511561318353057141

theorem tailTrace_5603030 : CollatzResearch.WordTrace tailWord_5603030 prefixEnd_5603030 2877047511561318353057141 := by
  unfold tailWord_5603030
  simp only [CollatzResearch.WordTrace]
  refine ⟨12772455805699169136544409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136239528594124470789807029 12772455805699169136544409)
  ·
    refine ⟨9579341854274376852408307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12772455805699169136544409 9579341854274376852408307)
    ·
      refine ⟨14369012781411565278612461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9579341854274376852408307 14369012781411565278612461)
      ·
        refine ⟨5388379793029336979479673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14369012781411565278612461 5388379793029336979479673)
        ·
          refine ⟨4041284844772002734609755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5388379793029336979479673 4041284844772002734609755)
          ·
            refine ⟨6061927267158004101914633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4041284844772002734609755 6061927267158004101914633)
            ·
              refine ⟨4546445450368503076435975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6061927267158004101914633 4546445450368503076435975)
              ·
                refine ⟨6819668175552754614653963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4546445450368503076435975 6819668175552754614653963)
                ·
                  refine ⟨10229502263329131921980945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6819668175552754614653963 10229502263329131921980945)
                  ·
                    refine ⟨7672126697496848941485709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10229502263329131921980945 7672126697496848941485709)
                    ·
                      refine ⟨2877047511561318353057141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7672126697496848941485709 2877047511561318353057141)
                      ·
                        rfl

theorem cell23_5603030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_5603030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603030 prefixEnd_5603030 := by exact prefixLift 5603030
  have htrace : WordTrace (prefixWord ++ tailWord_5603030) baseStart_5603030 baseEnd_5603030 := by
    simpa [prefixWord, tailWord_5603030, baseEnd_5603030] using wordTrace_append hprefix tailTrace_5603030
  have hstable : (prefixWord ++ tailWord_5603030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603030).length < 2 ^ (prefixWord ++ tailWord_5603030).sum := by decide
  have hdescent : baseEnd_5603030 < baseStart_5603030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603032 : List Nat := [2, 1, 2, 2, 3, 1, 2, 2, 4, 2, 2]
def baseStart_5603032 : Nat := 118140960795 + 5603032 * 2 ^ 59
def prefixEnd_5603032 : Nat := 4983230072969 + 3 ^ 40 * 5603032 * 2
def baseEnd_5603032 : Nat := 2877048538522627345232131

theorem tailTrace_5603032 : CollatzResearch.WordTrace tailWord_5603032 prefixEnd_5603032 2877048538522627345232131 := by
  unfold tailWord_5603032
  simp only [CollatzResearch.WordTrace]
  refine ⟨102179682918589730263141675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136239577224786307017522233 102179682918589730263141675)
  ·
    refine ⟨153269524377884595394712513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102179682918589730263141675 153269524377884595394712513)
    ·
      refine ⟨114952143283413446546034385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153269524377884595394712513 114952143283413446546034385)
      ·
        refine ⟨86214107462560084909525789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114952143283413446546034385 86214107462560084909525789)
        ·
          refine ⟨32330290298460031841072171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86214107462560084909525789 32330290298460031841072171)
          ·
            refine ⟨48495435447690047761608257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32330290298460031841072171 48495435447690047761608257)
            ·
              refine ⟨36371576585767535821206193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48495435447690047761608257 36371576585767535821206193)
              ·
                refine ⟨27278682439325651865904645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36371576585767535821206193 27278682439325651865904645)
                ·
                  refine ⟨5114752957373559724857121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27278682439325651865904645 5114752957373559724857121)
                  ·
                    refine ⟨3836064718030169793642841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5114752957373559724857121 3836064718030169793642841)
                    ·
                      refine ⟨2877048538522627345232131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3836064718030169793642841 2877048538522627345232131)
                      ·
                        rfl

theorem cell23_5603032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 4, 2, 2].length) (baseStart_5603032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603032 prefixEnd_5603032 := by exact prefixLift 5603032
  have htrace : WordTrace (prefixWord ++ tailWord_5603032) baseStart_5603032 baseEnd_5603032 := by
    simpa [prefixWord, tailWord_5603032, baseEnd_5603032] using wordTrace_append hprefix tailTrace_5603032
  have hstable : (prefixWord ++ tailWord_5603032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603032).length < 2 ^ (prefixWord ++ tailWord_5603032).sum := by decide
  have hdescent : baseEnd_5603032 < baseStart_5603032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603036 : List Nat := [2, 2, 5, 1, 2, 1, 1, 3, 1, 3, 2]
def baseStart_5603036 : Nat := 118140960795 + 5603036 * 2 ^ 59
def prefixEnd_5603036 : Nat := 4983230072969 + 3 ^ 40 * 5603036 * 2
def baseEnd_5603036 : Nat := 2877050592445245329582113

theorem tailTrace_5603036 : CollatzResearch.WordTrace tailWord_5603036 prefixEnd_5603036 2877050592445245329582113 := by
  unfold tailWord_5603036
  simp only [CollatzResearch.WordTrace]
  refine ⟨102179755864582484604714481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136239674486109979472952641 102179755864582484604714481)
  ·
    refine ⟨76634816898436863453535861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102179755864582484604714481 76634816898436863453535861)
    ·
      refine ⟨7184514084228455948768987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76634816898436863453535861 7184514084228455948768987)
      ·
        refine ⟨10776771126342683923153481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7184514084228455948768987 10776771126342683923153481)
        ·
          refine ⟨8082578344757012942365111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10776771126342683923153481 8082578344757012942365111)
          ·
            refine ⟨12123867517135519413547667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8082578344757012942365111 12123867517135519413547667)
            ·
              refine ⟨18185801275703279120321501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12123867517135519413547667 18185801275703279120321501)
              ·
                refine ⟨6819675478388729670120563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18185801275703279120321501 6819675478388729670120563)
                ·
                  refine ⟨10229513217583094505180845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6819675478388729670120563 10229513217583094505180845)
                  ·
                    refine ⟨3836067456593660439442817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10229513217583094505180845 3836067456593660439442817)
                    ·
                      refine ⟨2877050592445245329582113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3836067456593660439442817 2877050592445245329582113)
                      ·
                        rfl

theorem cell23_5603036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_5603036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603036 prefixEnd_5603036 := by exact prefixLift 5603036
  have htrace : WordTrace (prefixWord ++ tailWord_5603036) baseStart_5603036 baseEnd_5603036 := by
    simpa [prefixWord, tailWord_5603036, baseEnd_5603036] using wordTrace_append hprefix tailTrace_5603036
  have hstable : (prefixWord ++ tailWord_5603036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603036).length < 2 ^ (prefixWord ++ tailWord_5603036).sum := by decide
  have hdescent : baseEnd_5603036 < baseStart_5603036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603055 : List Nat := [1, 1, 2, 1, 5, 1, 1, 6, 5]
def baseStart_5603055 : Nat := 118140960795 + 5603055 * 2 ^ 59
def prefixEnd_5603055 : Nat := 4983230072969 + 3 ^ 40 * 5603055 * 2
def baseEnd_5603055 : Nat := 319673372064186750582725

theorem tailTrace_5603055 : CollatzResearch.WordTrace tailWord_5603055 prefixEnd_5603055 319673372064186750582725 := by
  unfold tailWord_5603055
  simp only [CollatzResearch.WordTrace]
  refine ⟨204360204716096135454370619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136240136477397423636247079 204360204716096135454370619)
  ·
    refine ⟨306540307074144203181555929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204360204716096135454370619 306540307074144203181555929)
    ·
      refine ⟨229905230305608152386166947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306540307074144203181555929 229905230305608152386166947)
      ·
        refine ⟨344857845458412228579250421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229905230305608152386166947 344857845458412228579250421)
        ·
          refine ⟨32330423011726146429304727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 344857845458412228579250421 32330423011726146429304727)
          ·
            refine ⟨48495634517589219643957091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32330423011726146429304727 48495634517589219643957091)
            ·
              refine ⟨72743451776383829465935637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48495634517589219643957091 72743451776383829465935637)
              ·
                refine ⟨3409849302017992006215733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72743451776383829465935637 3409849302017992006215733)
                ·
                  refine ⟨319673372064186750582725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3409849302017992006215733 319673372064186750582725)
                  ·
                    rfl

theorem cell23_5603055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 6, 5].length) (baseStart_5603055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603055 prefixEnd_5603055 := by exact prefixLift 5603055
  have htrace : WordTrace (prefixWord ++ tailWord_5603055) baseStart_5603055 baseEnd_5603055 := by
    simpa [prefixWord, tailWord_5603055, baseEnd_5603055] using wordTrace_append hprefix tailTrace_5603055
  have hstable : (prefixWord ++ tailWord_5603055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603055).length < 2 ^ (prefixWord ++ tailWord_5603055).sum := by decide
  have hdescent : baseEnd_5603055 < baseStart_5603055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603068 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 3, 7]
def baseStart_5603068 : Nat := 118140960795 + 5603068 * 2 ^ 59
def prefixEnd_5603068 : Nat := 4983230072969 + 3 ^ 40 * 5603068 * 2
def baseEnd_5603068 : Nat := 959022341275396401460655

theorem tailTrace_5603068 : CollatzResearch.WordTrace tailWord_5603068 prefixEnd_5603068 959022341275396401460655 := by
  unfold tailWord_5603068
  simp only [CollatzResearch.WordTrace]
  refine ⟨102180339432524519337296929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136240452576699359116395905 102180339432524519337296929)
  ·
    refine ⟨76635254574393389502972697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102180339432524519337296929 76635254574393389502972697)
    ·
      refine ⟨57476440930795042127229523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76635254574393389502972697 57476440930795042127229523)
      ·
        refine ⟨86214661396192563190844285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57476440930795042127229523 86214661396192563190844285)
        ·
          refine ⟨32330498023572211196566607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86214661396192563190844285 32330498023572211196566607)
          ·
            refine ⟨48495747035358316794849911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32330498023572211196566607 48495747035358316794849911)
            ·
              refine ⟨72743620553037475192274867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48495747035358316794849911 72743620553037475192274867)
              ·
                refine ⟨109115430829556212788412301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72743620553037475192274867 109115430829556212788412301)
                ·
                  refine ⟨40918286561083579795654613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109115430829556212788412301 40918286561083579795654613)
                  ·
                    refine ⟨959022341275396401460655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40918286561083579795654613 959022341275396401460655)
                    ·
                      rfl

theorem cell23_5603068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_5603068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603068 prefixEnd_5603068 := by exact prefixLift 5603068
  have htrace : WordTrace (prefixWord ++ tailWord_5603068) baseStart_5603068 baseEnd_5603068 := by
    simpa [prefixWord, tailWord_5603068, baseEnd_5603068] using wordTrace_append hprefix tailTrace_5603068
  have hstable : (prefixWord ++ tailWord_5603068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603068).length < 2 ^ (prefixWord ++ tailWord_5603068).sum := by decide
  have hdescent : baseEnd_5603068 < baseStart_5603068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603075 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 2, 5, 2]
def baseStart_5603075 : Nat := 118140960795 + 5603075 * 2 ^ 59
def prefixEnd_5603075 : Nat := 4983230072969 + 3 ^ 40 * 5603075 * 2
def baseEnd_5603075 : Nat := 2877070618190770676994433

theorem tailTrace_5603075 : CollatzResearch.WordTrace tailWord_5603075 prefixEnd_5603075 2877070618190770676994433 := by
  unfold tailWord_5603075
  simp only [CollatzResearch.WordTrace]
  refine ⟨204360934176023678870098679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136240622784015785913399119 204360934176023678870098679)
  ·
    refine ⟨306541401264035518305148019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204360934176023678870098679 306541401264035518305148019)
    ·
      refine ⟨459812101896053277457722029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306541401264035518305148019 459812101896053277457722029)
      ·
        refine ⟨172429538211019979046645761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 459812101896053277457722029 172429538211019979046645761)
        ·
          refine ⟨129322153658264984284984321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172429538211019979046645761 129322153658264984284984321)
          ·
            refine ⟨96991615243698738213738241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129322153658264984284984321 96991615243698738213738241)
            ·
              refine ⟨72743711432774053660303681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96991615243698738213738241 72743711432774053660303681)
              ·
                refine ⟨54557783574580540245227761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72743711432774053660303681 54557783574580540245227761)
                ·
                  refine ⟨40918337680935405183920821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54557783574580540245227761 40918337680935405183920821)
                  ·
                    refine ⟨3836094157587694235992577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40918337680935405183920821 3836094157587694235992577)
                    ·
                      refine ⟨2877070618190770676994433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3836094157587694235992577 2877070618190770676994433)
                      ·
                        rfl

theorem cell23_5603075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 5, 2].length) (baseStart_5603075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603075 prefixEnd_5603075 := by exact prefixLift 5603075
  have htrace : WordTrace (prefixWord ++ tailWord_5603075) baseStart_5603075 baseEnd_5603075 := by
    simpa [prefixWord, tailWord_5603075, baseEnd_5603075] using wordTrace_append hprefix tailTrace_5603075
  have hstable : (prefixWord ++ tailWord_5603075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603075).length < 2 ^ (prefixWord ++ tailWord_5603075).sum := by decide
  have hdescent : baseEnd_5603075 < baseStart_5603075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603105 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 4, 1, 4]
def baseStart_5603105 : Nat := 118140960795 + 5603105 * 2 ^ 59
def prefixEnd_5603105 : Nat := 4983230072969 + 3 ^ 40 * 5603105 * 2
def baseEnd_5603105 : Nat := 2877086022610405559619295

theorem tailTrace_5603105 : CollatzResearch.WordTrace tailWord_5603105 prefixEnd_5603105 2877086022610405559619295 := by
  unfold tailWord_5603105
  simp only [CollatzResearch.WordTrace]
  refine ⟨204362028365914993993690769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136241352243943329329127179 204362028365914993993690769)
  ·
    refine ⟨153271521274436245495268077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204362028365914993993690769 153271521274436245495268077)
    ·
      refine ⟨57476820477913592060725529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153271521274436245495268077 57476820477913592060725529)
      ·
        refine ⟨43107615358435194045544147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57476820477913592060725529 43107615358435194045544147)
        ·
          refine ⟨64661423037652791068316221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43107615358435194045544147 64661423037652791068316221)
          ·
            refine ⟨24248033639119796650618583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64661423037652791068316221 24248033639119796650618583)
            ·
              refine ⟨36372050458679694975927875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24248033639119796650618583 36372050458679694975927875)
              ·
                refine ⟨54558075688019542463891813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36372050458679694975927875 54558075688019542463891813)
                ·
                  refine ⟨10229639191503664211979715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54558075688019542463891813 10229639191503664211979715)
                  ·
                    refine ⟨15344458787255496317969573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10229639191503664211979715 15344458787255496317969573)
                    ·
                      refine ⟨2877086022610405559619295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15344458787255496317969573 2877086022610405559619295)
                      ·
                        rfl

theorem cell23_5603105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_5603105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603105 prefixEnd_5603105 := by exact prefixLift 5603105
  have htrace : WordTrace (prefixWord ++ tailWord_5603105) baseStart_5603105 baseEnd_5603105 := by
    simpa [prefixWord, tailWord_5603105, baseEnd_5603105] using wordTrace_append hprefix tailTrace_5603105
  have hstable : (prefixWord ++ tailWord_5603105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603105).length < 2 ^ (prefixWord ++ tailWord_5603105).sum := by decide
  have hdescent : baseEnd_5603105 < baseStart_5603105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603175 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 5, 5]
def baseStart_5603175 : Nat := 118140960795 + 5603175 * 2 ^ 59
def prefixEnd_5603175 : Nat := 4983230072969 + 3 ^ 40 * 5603175 * 2
def baseEnd_5603175 : Nat := 959040655418740095247991

theorem tailTrace_5603175 : CollatzResearch.WordTrace tailWord_5603175 prefixEnd_5603175 959040655418740095247991 := by
  unfold tailWord_5603175
  simp only [CollatzResearch.WordTrace]
  refine ⟨204364581475661395948738979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136243054317107597299159319 204364581475661395948738979)
  ·
    refine ⟨306546872213492093923108469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204364581475661395948738979 306546872213492093923108469)
    ·
      refine ⟨28738769270014883805291419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 306546872213492093923108469 28738769270014883805291419)
      ·
        refine ⟨43108153905022325707937129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28738769270014883805291419 43108153905022325707937129)
        ·
          refine ⟨32331115428766744280952847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43108153905022325707937129 32331115428766744280952847)
          ·
            refine ⟨48496673143150116421429271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32331115428766744280952847 48496673143150116421429271)
            ·
              refine ⟨72745009714725174632143907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48496673143150116421429271 72745009714725174632143907)
              ·
                refine ⟨109117514572087761948215861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72745009714725174632143907 109117514572087761948215861)
                ·
                  refine ⟨10229766991133227682645237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109117514572087761948215861 10229766991133227682645237)
                  ·
                    refine ⟨959040655418740095247991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10229766991133227682645237 959040655418740095247991)
                    ·
                      rfl

theorem cell23_5603175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_5603175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603175 prefixEnd_5603175 := by exact prefixLift 5603175
  have htrace : WordTrace (prefixWord ++ tailWord_5603175) baseStart_5603175 baseEnd_5603175 := by
    simpa [prefixWord, tailWord_5603175, baseEnd_5603175] using wordTrace_append hprefix tailTrace_5603175
  have hstable : (prefixWord ++ tailWord_5603175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603175).length < 2 ^ (prefixWord ++ tailWord_5603175).sum := by decide
  have hdescent : baseEnd_5603175 < baseStart_5603175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603189 : List Nat := [1, 3, 4, 1, 1, 1, 3, 2, 3, 1, 3]
def baseStart_5603189 : Nat := 118140960795 + 5603189 * 2 ^ 59
def prefixEnd_5603189 : Nat := 4983230072969 + 3 ^ 40 * 5603189 * 2
def baseEnd_5603189 : Nat := 2877129154985383230968909

theorem tailTrace_5603189 : CollatzResearch.WordTrace tailWord_5603189 prefixEnd_5603189 2877129154985383230968909 := by
  unfold tailWord_5603189
  simp only [CollatzResearch.WordTrace]
  refine ⟨204365092097610676339748621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136243394731740450893165747 204365092097610676339748621)
  ·
    refine ⟨76636909536604003627405733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204365092097610676339748621 76636909536604003627405733)
    ·
      refine ⟨14369420538113250680138575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76636909536604003627405733 14369420538113250680138575)
      ·
        refine ⟨21554130807169876020207863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14369420538113250680138575 21554130807169876020207863)
        ·
          refine ⟨32331196210754814030311795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21554130807169876020207863 32331196210754814030311795)
          ·
            refine ⟨48496794316132221045467693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32331196210754814030311795 48496794316132221045467693)
            ·
              refine ⟨18186297868549582892050385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48496794316132221045467693 18186297868549582892050385)
              ·
                refine ⟨13639723401412187169037789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18186297868549582892050385 13639723401412187169037789)
                ·
                  refine ⟨5114896275529570188389171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13639723401412187169037789 5114896275529570188389171)
                  ·
                    refine ⟨7672344413294355282583757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5114896275529570188389171 7672344413294355282583757)
                    ·
                      refine ⟨2877129154985383230968909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7672344413294355282583757 2877129154985383230968909)
                      ·
                        rfl

theorem cell23_5603189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_5603189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603189 prefixEnd_5603189 := by exact prefixLift 5603189
  have htrace : WordTrace (prefixWord ++ tailWord_5603189) baseStart_5603189 baseEnd_5603189 := by
    simpa [prefixWord, tailWord_5603189, baseEnd_5603189] using wordTrace_append hprefix tailTrace_5603189
  have hstable : (prefixWord ++ tailWord_5603189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603189).length < 2 ^ (prefixWord ++ tailWord_5603189).sum := by decide
  have hdescent : baseEnd_5603189 < baseStart_5603189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603205 : List Nat := [1, 3, 1, 1, 3, 2, 1, 4, 1, 6]
def baseStart_5603205 : Nat := 118140960795 + 5603205 * 2 ^ 59
def prefixEnd_5603205 : Nat := 4983230072969 + 3 ^ 40 * 5603205 * 2
def baseEnd_5603205 : Nat := 959045790225285056122945

theorem tailTrace_5603205 : CollatzResearch.WordTrace tailWord_5603205 prefixEnd_5603205 959045790225285056122945 := by
  unfold tailWord_5603205
  simp only [CollatzResearch.WordTrace]
  refine ⟨204365675665552711072331069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136243783777035140714887379 204365675665552711072331069)
  ·
    refine ⟨76637128374582266652124151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204365675665552711072331069 76637128374582266652124151)
    ·
      refine ⟨114955692561873399978186227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76637128374582266652124151 114955692561873399978186227)
      ·
        refine ⟨172433538842810099967279341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114955692561873399978186227 172433538842810099967279341)
        ·
          refine ⟨64662577066053787487729753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172433538842810099967279341 64662577066053787487729753)
          ·
            refine ⟨48496932799540340615797315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64662577066053787487729753 48496932799540340615797315)
            ·
              refine ⟨72745399199310510923695973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48496932799540340615797315 72745399199310510923695973)
              ·
                refine ⟨13639762349870720798192995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72745399199310510923695973 13639762349870720798192995)
                ·
                  refine ⟨20459643524806081197289493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13639762349870720798192995 20459643524806081197289493)
                  ·
                    refine ⟨959045790225285056122945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20459643524806081197289493 959045790225285056122945)
                    ·
                      rfl

theorem cell23_5603205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 6].length) (baseStart_5603205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603205 prefixEnd_5603205 := by exact prefixLift 5603205
  have htrace : WordTrace (prefixWord ++ tailWord_5603205) baseStart_5603205 baseEnd_5603205 := by
    simpa [prefixWord, tailWord_5603205, baseEnd_5603205] using wordTrace_append hprefix tailTrace_5603205
  have hstable : (prefixWord ++ tailWord_5603205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603205).length < 2 ^ (prefixWord ++ tailWord_5603205).sum := by decide
  have hdescent : baseEnd_5603205 < baseStart_5603205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603225 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 3, 2, 4]
def baseStart_5603225 : Nat := 118140960795 + 5603225 * 2 ^ 59
def prefixEnd_5603225 : Nat := 4983230072969 + 3 ^ 40 * 5603225 * 2
def baseEnd_5603225 : Nat := 2877147640288945090118743

theorem tailTrace_5603225 : CollatzResearch.WordTrace tailWord_5603225 prefixEnd_5603225 2877147640288945090118743 := by
  unfold tailWord_5603225
  simp only [CollatzResearch.WordTrace]
  refine ⟨204366405125480254488059129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136244270083653502992039419 204366405125480254488059129)
  ·
    refine ⟨153274803844110190866044347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204366405125480254488059129 153274803844110190866044347)
    ·
      refine ⟨229912205766165286299066521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153274803844110190866044347 229912205766165286299066521)
      ·
        refine ⟨172434154324623964724299891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229912205766165286299066521 172434154324623964724299891)
        ·
          refine ⟨258651231486935947086449837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172434154324623964724299891 258651231486935947086449837)
          ·
            refine ⟨96994211807600980157418689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 258651231486935947086449837 96994211807600980157418689)
            ·
              refine ⟨72745658855700735118064017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96994211807600980157418689 72745658855700735118064017)
              ·
                refine ⟨54559244141775551338548013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72745658855700735118064017 54559244141775551338548013)
                ·
                  refine ⟨20459716553165831751955505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54559244141775551338548013 20459716553165831751955505)
                  ·
                    refine ⟨15344787414874373813966629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20459716553165831751955505 15344787414874373813966629)
                    ·
                      refine ⟨2877147640288945090118743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15344787414874373813966629 2877147640288945090118743)
                      ·
                        rfl

theorem cell23_5603225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_5603225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603225 prefixEnd_5603225 := by exact prefixLift 5603225
  have htrace : WordTrace (prefixWord ++ tailWord_5603225) baseStart_5603225 baseEnd_5603225 := by
    simpa [prefixWord, tailWord_5603225, baseEnd_5603225] using wordTrace_append hprefix tailTrace_5603225
  have hstable : (prefixWord ++ tailWord_5603225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603225).length < 2 ^ (prefixWord ++ tailWord_5603225).sum := by decide
  have hdescent : baseEnd_5603225 < baseStart_5603225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603239 : List Nat := [1, 1, 6, 1, 2, 3, 1, 1, 1, 6]
def baseStart_5603239 : Nat := 118140960795 + 5603239 * 2 ^ 59
def prefixEnd_5603239 : Nat := 4983230072969 + 3 ^ 40 * 5603239 * 2
def baseEnd_5603239 : Nat := 959051609672702678447893

theorem tailTrace_5603239 : CollatzResearch.WordTrace tailWord_5603239 prefixEnd_5603239 959051609672702678447893 := by
  unfold tailWord_5603239
  simp only [CollatzResearch.WordTrace]
  refine ⟨204366915747429534879068771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136244610498286356586045847 204366915747429534879068771)
  ·
    refine ⟨306550373621144302318603157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204366915747429534879068771 306550373621144302318603157)
    ·
      refine ⟨14369548763491139171184523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 306550373621144302318603157 14369548763491139171184523)
      ·
        refine ⟨21554323145236708756776785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14369548763491139171184523 21554323145236708756776785)
        ·
          refine ⟨16165742358927531567582589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21554323145236708756776785 16165742358927531567582589)
          ·
            refine ⟨6062153384597824337843471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16165742358927531567582589 6062153384597824337843471)
            ·
              refine ⟨9093230076896736506765207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6062153384597824337843471 9093230076896736506765207)
              ·
                refine ⟨13639845115345104760147811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9093230076896736506765207 13639845115345104760147811)
                ·
                  refine ⟨20459767673017657140221717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13639845115345104760147811 20459767673017657140221717)
                  ·
                    refine ⟨959051609672702678447893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20459767673017657140221717 959051609672702678447893)
                    ·
                      rfl

theorem cell23_5603239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_5603239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603239 prefixEnd_5603239 := by exact prefixLift 5603239
  have htrace : WordTrace (prefixWord ++ tailWord_5603239) baseStart_5603239 baseEnd_5603239 := by
    simpa [prefixWord, tailWord_5603239, baseEnd_5603239] using wordTrace_append hprefix tailTrace_5603239
  have hstable : (prefixWord ++ tailWord_5603239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603239).length < 2 ^ (prefixWord ++ tailWord_5603239).sum := by decide
  have hdescent : baseEnd_5603239 < baseStart_5603239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603249 : List Nat := [1, 2, 2, 4, 2, 1, 1, 4, 1, 2, 3]
def baseStart_5603249 : Nat := 118140960795 + 5603249 * 2 ^ 59
def prefixEnd_5603249 : Nat := 4983230072969 + 3 ^ 40 * 5603249 * 2
def baseEnd_5603249 : Nat := 2877159963824652996218633

theorem tailTrace_5603249 : CollatzResearch.WordTrace tailWord_5603249 prefixEnd_5603249 2877159963824652996218633 := by
  unfold tailWord_5603249
  simp only [CollatzResearch.WordTrace]
  refine ⟨204367280477393306586932801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136244853651595537724621867 204367280477393306586932801)
  ·
    refine ⟨153275460358044979940199601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204367280477393306586932801 153275460358044979940199601)
    ·
      refine ⟨114956595268533734955149701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153275460358044979940199601 114956595268533734955149701)
      ·
        refine ⟨21554361612850075304090569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114956595268533734955149701 21554361612850075304090569)
        ·
          refine ⟨16165771209637556478067927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21554361612850075304090569 16165771209637556478067927)
          ·
            refine ⟨24248656814456334717101891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16165771209637556478067927 24248656814456334717101891)
            ·
              refine ⟨36372985221684502075652837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24248656814456334717101891 36372985221684502075652837)
              ·
                refine ⟨6819934729065844139184907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36372985221684502075652837 6819934729065844139184907)
                ·
                  refine ⟨10229902093598766208777361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6819934729065844139184907 10229902093598766208777361)
                  ·
                    refine ⟨7672426570199074656583021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10229902093598766208777361 7672426570199074656583021)
                    ·
                      refine ⟨2877159963824652996218633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7672426570199074656583021 2877159963824652996218633)
                      ·
                        rfl

theorem cell23_5603249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_5603249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603249 prefixEnd_5603249 := by exact prefixLift 5603249
  have htrace : WordTrace (prefixWord ++ tailWord_5603249) baseStart_5603249 baseEnd_5603249 := by
    simpa [prefixWord, tailWord_5603249, baseEnd_5603249] using wordTrace_append hprefix tailTrace_5603249
  have hstable : (prefixWord ++ tailWord_5603249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603249).length < 2 ^ (prefixWord ++ tailWord_5603249).sum := by decide
  have hdescent : baseEnd_5603249 < baseStart_5603249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603275 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 5]
def baseStart_5603275 : Nat := 118140960795 + 5603275 * 2 ^ 59
def prefixEnd_5603275 : Nat := 4983230072969 + 3 ^ 40 * 5603275 * 2
def baseEnd_5603275 : Nat := 2877173314321669894493513

theorem tailTrace_5603275 : CollatzResearch.WordTrace tailWord_5603275 prefixEnd_5603275 2877173314321669894493513 := by
  unfold tailWord_5603275
  simp only [CollatzResearch.WordTrace]
  refine ⟨204368228775299113027379279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136245485850199408684919519 204368228775299113027379279)
  ·
    refine ⟨306552343162948669541068919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204368228775299113027379279 306552343162948669541068919)
    ·
      refine ⟨459828514744423004311603379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306552343162948669541068919 459828514744423004311603379)
      ·
        refine ⟨689742772116634506467405069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459828514744423004311603379 689742772116634506467405069)
        ·
          refine ⟨258653539543737939925276901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 689742772116634506467405069 258653539543737939925276901)
          ·
            refine ⟨48497538664450863735989419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 258653539543737939925276901 48497538664450863735989419)
            ·
              refine ⟨72746307996676295603984129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48497538664450863735989419 72746307996676295603984129)
              ·
                refine ⟨54559730997507221702988097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72746307996676295603984129 54559730997507221702988097)
                ·
                  refine ⟨40919798248130416277241073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54559730997507221702988097 40919798248130416277241073)
                  ·
                    refine ⟨30689848686097812207930805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40919798248130416277241073 30689848686097812207930805)
                    ·
                      refine ⟨2877173314321669894493513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30689848686097812207930805 2877173314321669894493513)
                      ·
                        rfl

theorem cell23_5603275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 5].length) (baseStart_5603275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603275 prefixEnd_5603275 := by exact prefixLift 5603275
  have htrace : WordTrace (prefixWord ++ tailWord_5603275) baseStart_5603275 baseEnd_5603275 := by
    simpa [prefixWord, tailWord_5603275, baseEnd_5603275] using wordTrace_append hprefix tailTrace_5603275
  have hstable : (prefixWord ++ tailWord_5603275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603275).length < 2 ^ (prefixWord ++ tailWord_5603275).sum := by decide
  have hdescent : baseEnd_5603275 < baseStart_5603275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603279 : List Nat := [1, 1, 2, 1, 1, 5, 2, 4, 2, 1, 3]
def baseStart_5603279 : Nat := 118140960795 + 5603279 * 2 ^ 59
def prefixEnd_5603279 : Nat := 4983230072969 + 3 ^ 40 * 5603279 * 2
def baseEnd_5603279 : Nat := 2877175368244287878843495

theorem tailTrace_5603279 : CollatzResearch.WordTrace tailWord_5603279 prefixEnd_5603279 2877175368244287878843495 := by
  unfold tailWord_5603279
  simp only [CollatzResearch.WordTrace]
  refine ⟨204368374667284621710524891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136245583111523081140349927 204368374667284621710524891)
  ·
    refine ⟨306552562000926932565787337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204368374667284621710524891 306552562000926932565787337)
    ·
      refine ⟨229914421500695199424340503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306552562000926932565787337 229914421500695199424340503)
      ·
        refine ⟨344871632251042799136510755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229914421500695199424340503 344871632251042799136510755)
        ·
          refine ⟨517307448376564198704766133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344871632251042799136510755 517307448376564198704766133)
          ·
            refine ⟨48497573285302893628571825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 517307448376564198704766133 48497573285302893628571825)
            ·
              refine ⟨36373179963977170221428869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48497573285302893628571825 36373179963977170221428869)
              ·
                refine ⟨6819971243245719416517913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36373179963977170221428869 6819971243245719416517913)
                ·
                  refine ⟨5114978432434289562388435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6819971243245719416517913 5114978432434289562388435)
                  ·
                    refine ⟨7672467648651434343582653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5114978432434289562388435 7672467648651434343582653)
                    ·
                      refine ⟨2877175368244287878843495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7672467648651434343582653 2877175368244287878843495)
                      ·
                        rfl

theorem cell23_5603279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 2, 1, 3].length) (baseStart_5603279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603279 prefixEnd_5603279 := by exact prefixLift 5603279
  have htrace : WordTrace (prefixWord ++ tailWord_5603279) baseStart_5603279 baseEnd_5603279 := by
    simpa [prefixWord, tailWord_5603279, baseEnd_5603279] using wordTrace_append hprefix tailTrace_5603279
  have hstable : (prefixWord ++ tailWord_5603279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603279).length < 2 ^ (prefixWord ++ tailWord_5603279).sum := by decide
  have hdescent : baseEnd_5603279 < baseStart_5603279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603342 : List Nat := [4, 1, 1, 2, 2, 1, 2, 3, 7]
def baseStart_5603342 : Nat := 118140960795 + 5603342 * 2 ^ 59
def prefixEnd_5603342 : Nat := 4983230072969 + 3 ^ 40 * 5603342 * 2
def baseEnd_5603342 : Nat := 319689746391724570261745

theorem tailTrace_5603342 : CollatzResearch.WordTrace tailWord_5603342 prefixEnd_5603342 319689746391724570261745 := by
  unfold tailWord_5603342
  simp only [CollatzResearch.WordTrace]
  refine ⟨25546334058257047933758535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136247114977370922313378853 25546334058257047933758535)
  ·
    refine ⟨38319501087385571900637803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25546334058257047933758535 38319501087385571900637803)
    ·
      refine ⟨57479251631078357850956705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38319501087385571900637803 57479251631078357850956705)
      ·
        refine ⟨43109438723308768388217529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57479251631078357850956705 43109438723308768388217529)
        ·
          refine ⟨32332079042481576291163147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43109438723308768388217529 32332079042481576291163147)
          ·
            refine ⟨48498118563722364436744721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32332079042481576291163147 48498118563722364436744721)
            ·
              refine ⟨36373588922791773327558541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48498118563722364436744721 36373588922791773327558541)
              ·
                refine ⟨13640095846046914997834453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36373588922791773327558541 13640095846046914997834453)
                ·
                  refine ⟨319689746391724570261745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13640095846046914997834453 319689746391724570261745)
                  ·
                    rfl

theorem cell23_5603342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 7].length) (baseStart_5603342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603342 prefixEnd_5603342 := by exact prefixLift 5603342
  have htrace : WordTrace (prefixWord ++ tailWord_5603342) baseStart_5603342 baseEnd_5603342 := by
    simpa [prefixWord, tailWord_5603342, baseEnd_5603342] using wordTrace_append hprefix tailTrace_5603342
  have hstable : (prefixWord ++ tailWord_5603342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603342).length < 2 ^ (prefixWord ++ tailWord_5603342).sum := by decide
  have hdescent : baseEnd_5603342 < baseStart_5603342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603345 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 8]
def baseStart_5603345 : Nat := 118140960795 + 5603345 * 2 ^ 59
def prefixEnd_5603345 : Nat := 4983230072969 + 3 ^ 40 * 5603345 * 2
def baseEnd_5603345 : Nat := 2877209257967484620618191

theorem tailTrace_5603345 : CollatzResearch.WordTrace tailWord_5603345 prefixEnd_5603345 2877209257967484620618191 := by
  unfold tailWord_5603345
  simp only [CollatzResearch.WordTrace]
  refine ⟨204370781885045514982427489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136247187923363676654951659 204370781885045514982427489)
  ·
    refine ⟨153278086413784136236820617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204370781885045514982427489 153278086413784136236820617)
    ·
      refine ⟨114958564810338102177615463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153278086413784136236820617 114958564810338102177615463)
      ·
        refine ⟨172437847215507153266423195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114958564810338102177615463 172437847215507153266423195)
        ·
          refine ⟨258656770823260729899634793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172437847215507153266423195 258656770823260729899634793)
          ·
            refine ⟨193992578117445547424726095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258656770823260729899634793 193992578117445547424726095)
            ·
              refine ⟨290988867176168321137089143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193992578117445547424726095 290988867176168321137089143)
              ·
                refine ⟨436483300764252481705633715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290988867176168321137089143 436483300764252481705633715)
                ·
                  refine ⟨654724951146378722558450573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 436483300764252481705633715 654724951146378722558450573)
                  ·
                    refine ⟨245521856679892020959418965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 654724951146378722558450573 245521856679892020959418965)
                    ·
                      refine ⟨2877209257967484620618191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 245521856679892020959418965 2877209257967484620618191)
                      ·
                        rfl

theorem cell23_5603345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_5603345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603345 prefixEnd_5603345 := by exact prefixLift 5603345
  have htrace : WordTrace (prefixWord ++ tailWord_5603345) baseStart_5603345 baseEnd_5603345 := by
    simpa [prefixWord, tailWord_5603345, baseEnd_5603345] using wordTrace_append hprefix tailTrace_5603345
  have hstable : (prefixWord ++ tailWord_5603345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603345).length < 2 ^ (prefixWord ++ tailWord_5603345).sum := by decide
  have hdescent : baseEnd_5603345 < baseStart_5603345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603349 : List Nat := [1, 3, 2, 1, 5, 1, 1, 1, 2, 2, 4]
def baseStart_5603349 : Nat := 118140960795 + 5603349 * 2 ^ 59
def prefixEnd_5603349 : Nat := 4983230072969 + 3 ^ 40 * 5603349 * 2
def baseEnd_5603349 : Nat := 2877211311890102604968173

theorem tailTrace_5603349 : CollatzResearch.WordTrace tailWord_5603349 prefixEnd_5603349 2877211311890102604968173 := by
  unfold tailWord_5603349
  simp only [CollatzResearch.WordTrace]
  refine ⟨204370927777031023665573101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136247285184687349110382067 204370927777031023665573101)
  ·
    refine ⟨76639097916386633874589913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204370927777031023665573101 76639097916386633874589913)
    ·
      refine ⟨57479323437289975405942435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76639097916386633874589913 57479323437289975405942435)
      ·
        refine ⟨86218985155934963108913653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57479323437289975405942435 86218985155934963108913653)
        ·
          refine ⟨8083029858368902791460655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86218985155934963108913653 8083029858368902791460655)
          ·
            refine ⟨12124544787553354187190983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8083029858368902791460655 12124544787553354187190983)
            ·
              refine ⟨18186817181330031280786475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12124544787553354187190983 18186817181330031280786475)
              ·
                refine ⟨27280225771995046921179713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18186817181330031280786475 27280225771995046921179713)
                ·
                  refine ⟨20460169328996285190884785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27280225771995046921179713 20460169328996285190884785)
                  ·
                    refine ⟨15345126996747213893163589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20460169328996285190884785 15345126996747213893163589)
                    ·
                      refine ⟨2877211311890102604968173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15345126996747213893163589 2877211311890102604968173)
                      ·
                        rfl

theorem cell23_5603349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_5603349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603349 prefixEnd_5603349 := by exact prefixLift 5603349
  have htrace : WordTrace (prefixWord ++ tailWord_5603349) baseStart_5603349 baseEnd_5603349 := by
    simpa [prefixWord, tailWord_5603349, baseEnd_5603349] using wordTrace_append hprefix tailTrace_5603349
  have hstable : (prefixWord ++ tailWord_5603349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603349).length < 2 ^ (prefixWord ++ tailWord_5603349).sum := by decide
  have hdescent : baseEnd_5603349 < baseStart_5603349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603372 : List Nat := [2, 2, 1, 1, 1, 2, 2, 5, 2, 5]
def baseStart_5603372 : Nat := 118140960795 + 5603372 * 2 ^ 59
def prefixEnd_5603372 : Nat := 4983230072969 + 3 ^ 40 * 5603372 * 2
def baseEnd_5603372 : Nat := 959074373981718671660189

theorem tailTrace_5603372 : CollatzResearch.WordTrace tailWord_5603372 prefixEnd_5603372 959074373981718671660189 := by
  unfold tailWord_5603372
  simp only [CollatzResearch.WordTrace]
  refine ⟨102185883327973849296830185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136247844437298465729106913 102185883327973849296830185)
  ·
    refine ⟨76639412495980386972622639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102185883327973849296830185 76639412495980386972622639)
    ·
      refine ⟨114959118743970580458933959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76639412495980386972622639 114959118743970580458933959)
      ·
        refine ⟨172438678115955870688400939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114959118743970580458933959 172438678115955870688400939)
        ·
          refine ⟨258658017173933806032601409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172438678115955870688400939 258658017173933806032601409)
          ·
            refine ⟨193993512880450354524451057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258658017173933806032601409 193993512880450354524451057)
            ·
              refine ⟨145495134660337765893338293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193993512880450354524451057 145495134660337765893338293)
              ·
                refine ⟨13640168874406665552500465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145495134660337765893338293 13640168874406665552500465)
                ·
                  refine ⟨10230126655804999164375349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13640168874406665552500465 10230126655804999164375349)
                  ·
                    refine ⟨959074373981718671660189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10230126655804999164375349 959074373981718671660189)
                    ·
                      rfl

theorem cell23_5603372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 5].length) (baseStart_5603372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603372 prefixEnd_5603372 := by exact prefixLift 5603372
  have htrace : WordTrace (prefixWord ++ tailWord_5603372) baseStart_5603372 baseEnd_5603372 := by
    simpa [prefixWord, tailWord_5603372, baseEnd_5603372] using wordTrace_append hprefix tailTrace_5603372
  have hstable : (prefixWord ++ tailWord_5603372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603372).length < 2 ^ (prefixWord ++ tailWord_5603372).sum := by decide
  have hdescent : baseEnd_5603372 < baseStart_5603372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603429 : List Nat := [1, 3, 1, 3, 2, 2, 2, 1, 1, 4, 3]
def baseStart_5603429 : Nat := 118140960795 + 5603429 * 2 ^ 59
def prefixEnd_5603429 : Nat := 4983230072969 + 3 ^ 40 * 5603429 * 2
def baseEnd_5603429 : Nat := 2877252390342462291967805

theorem tailTrace_5603429 : CollatzResearch.WordTrace tailWord_5603429 prefixEnd_5603429 2877252390342462291967805 := by
  unfold tailWord_5603429
  simp only [CollatzResearch.WordTrace]
  refine ⟨204373845616741197328485341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136249230411160798218990227 204373845616741197328485341)
  ·
    refine ⟨76640192106277948998182003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204373845616741197328485341 76640192106277948998182003)
    ·
      refine ⟨114960288159416923497273005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76640192106277948998182003 114960288159416923497273005)
      ·
        refine ⟨43110108059781346311477377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114960288159416923497273005 43110108059781346311477377)
        ·
          refine ⟨32332581044836009733608033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43110108059781346311477377 32332581044836009733608033)
          ·
            refine ⟨24249435783627007300206025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32332581044836009733608033 24249435783627007300206025)
            ·
              refine ⟨18187076837720255475154519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24249435783627007300206025 18187076837720255475154519)
              ·
                refine ⟨27280615256580383212731779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18187076837720255475154519 27280615256580383212731779)
                ·
                  refine ⟨40920922884870574819097669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27280615256580383212731779 40920922884870574819097669)
                  ·
                    refine ⟨7672673040913232778580813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40920922884870574819097669 7672673040913232778580813)
                    ·
                      refine ⟨2877252390342462291967805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7672673040913232778580813 2877252390342462291967805)
                      ·
                        rfl

theorem cell23_5603429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_5603429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603429 prefixEnd_5603429 := by exact prefixLift 5603429
  have htrace : WordTrace (prefixWord ++ tailWord_5603429) baseStart_5603429 baseEnd_5603429 := by
    simpa [prefixWord, tailWord_5603429, baseEnd_5603429] using wordTrace_append hprefix tailTrace_5603429
  have hstable : (prefixWord ++ tailWord_5603429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603429).length < 2 ^ (prefixWord ++ tailWord_5603429).sum := by decide
  have hdescent : baseEnd_5603429 < baseStart_5603429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603446 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3]
def baseStart_5603446 : Nat := 118140960795 + 5603446 * 2 ^ 59
def prefixEnd_5603446 : Nat := 4983230072969 + 3 ^ 40 * 5603446 * 2
def baseEnd_5603446 : Nat := 2877261119513588725455227

theorem tailTrace_5603446 : CollatzResearch.WordTrace tailWord_5603446 prefixEnd_5603446 2877261119513588725455227 := by
  unfold tailWord_5603446
  simp only [CollatzResearch.WordTrace]
  refine ⟨12773404103604975576990887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136249643771786406154569461 12773404103604975576990887)
  ·
    refine ⟨19160106155407463365486331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12773404103604975576990887 19160106155407463365486331)
    ·
      refine ⟨28740159233111195048229497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19160106155407463365486331 28740159233111195048229497)
      ·
        refine ⟨21555119424833396286172123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28740159233111195048229497 21555119424833396286172123)
        ·
          refine ⟨32332679137250094429258185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21555119424833396286172123 32332679137250094429258185)
          ·
            refine ⟨24249509352937570821943639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32332679137250094429258185 24249509352937570821943639)
            ·
              refine ⟨36374264029406356232915459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24249509352937570821943639 36374264029406356232915459)
              ·
                refine ⟨54561396044109534349373189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36374264029406356232915459 54561396044109534349373189)
                ·
                  refine ⟨10230261758270537690507473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54561396044109534349373189 10230261758270537690507473)
                  ·
                    refine ⟨7672696318702903267880605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10230261758270537690507473 7672696318702903267880605)
                    ·
                      refine ⟨2877261119513588725455227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7672696318702903267880605 2877261119513588725455227)
                      ·
                        rfl

theorem cell23_5603446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_5603446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603446 prefixEnd_5603446 := by exact prefixLift 5603446
  have htrace : WordTrace (prefixWord ++ tailWord_5603446) baseStart_5603446 baseEnd_5603446 := by
    simpa [prefixWord, tailWord_5603446, baseEnd_5603446] using wordTrace_append hprefix tailTrace_5603446
  have hstable : (prefixWord ++ tailWord_5603446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603446).length < 2 ^ (prefixWord ++ tailWord_5603446).sum := by decide
  have hdescent : baseEnd_5603446 < baseStart_5603446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603466 : List Nat := [3, 1, 2, 3, 1, 2, 4, 1, 6]
def baseStart_5603466 : Nat := 118140960795 + 5603466 * 2 ^ 59
def prefixEnd_5603466 : Nat := 4983230072969 + 3 ^ 40 * 5603466 * 2
def baseEnd_5603466 : Nat := 319696821014075405245015

theorem tailTrace_5603466 : CollatzResearch.WordTrace tailWord_5603466 prefixEnd_5603466 319696821014075405245015 := by
  unfold tailWord_5603466
  simp only [CollatzResearch.WordTrace]
  refine ⟨51093798779401788161895563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136250130078404768431721501 51093798779401788161895563)
  ·
    refine ⟨76640698169102682242843345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51093798779401788161895563 76640698169102682242843345)
    ·
      refine ⟨57480523626827011682132509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76640698169102682242843345 57480523626827011682132509)
      ·
        refine ⟨21555196360060129380799691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57480523626827011682132509 21555196360060129380799691)
        ·
          refine ⟨32332794540090194071199537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21555196360060129380799691 32332794540090194071199537)
          ·
            refine ⟨24249595905067645553399653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32332794540090194071199537 24249595905067645553399653)
            ·
              refine ⟨4546799232200183541262435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24249595905067645553399653 4546799232200183541262435)
              ·
                refine ⟨6820198848300275311893653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4546799232200183541262435 6820198848300275311893653)
                ·
                  refine ⟨319696821014075405245015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6820198848300275311893653 319696821014075405245015)
                  ·
                    rfl

theorem cell23_5603466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 6].length) (baseStart_5603466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603466 prefixEnd_5603466 := by exact prefixLift 5603466
  have htrace : WordTrace (prefixWord ++ tailWord_5603466) baseStart_5603466 baseEnd_5603466 := by
    simpa [prefixWord, tailWord_5603466, baseEnd_5603466] using wordTrace_append hprefix tailTrace_5603466
  have hstable : (prefixWord ++ tailWord_5603466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603466).length < 2 ^ (prefixWord ++ tailWord_5603466).sum := by decide
  have hdescent : baseEnd_5603466 < baseStart_5603466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603493 : List Nat := [1, 3, 1, 2, 1, 3, 2, 5, 1, 1, 3]
def baseStart_5603493 : Nat := 118140960795 + 5603493 * 2 ^ 59
def prefixEnd_5603493 : Nat := 4983230072969 + 3 ^ 40 * 5603493 * 2
def baseEnd_5603493 : Nat := 2877285253104350041567511

theorem tailTrace_5603493 : CollatzResearch.WordTrace tailWord_5603493 prefixEnd_5603493 2877285253104350041567511 := by
  unfold tailWord_5603493
  simp only [CollatzResearch.WordTrace]
  refine ⟨204376179888509336258815133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136250786592339557505876755 204376179888509336258815133)
  ·
    refine ⟨76641067458191001097055675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204376179888509336258815133 76641067458191001097055675)
    ·
      refine ⟨114961601187286501645583513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76641067458191001097055675 114961601187286501645583513)
      ·
        refine ⟨86221200890464876234187635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114961601187286501645583513 86221200890464876234187635)
        ·
          refine ⟨129331801335697314351281453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86221200890464876234187635 129331801335697314351281453)
          ·
            refine ⟨48499425500886492881730545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129331801335697314351281453 48499425500886492881730545)
            ·
              refine ⟨36374569125664869661297909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48499425500886492881730545 36374569125664869661297909)
              ·
                refine ⟨3410115855531081530746679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36374569125664869661297909 3410115855531081530746679)
                ·
                  refine ⟨5115173783296622296120019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3410115855531081530746679 5115173783296622296120019)
                  ·
                    refine ⟨7672760674944933444180029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5115173783296622296120019 7672760674944933444180029)
                    ·
                      refine ⟨2877285253104350041567511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7672760674944933444180029 2877285253104350041567511)
                      ·
                        rfl

theorem cell23_5603493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 5, 1, 1, 3].length) (baseStart_5603493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603493 prefixEnd_5603493 := by exact prefixLift 5603493
  have htrace : WordTrace (prefixWord ++ tailWord_5603493) baseStart_5603493 baseEnd_5603493 := by
    simpa [prefixWord, tailWord_5603493, baseEnd_5603493] using wordTrace_append hprefix tailTrace_5603493
  have hstable : (prefixWord ++ tailWord_5603493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603493).length < 2 ^ (prefixWord ++ tailWord_5603493).sum := by decide
  have hdescent : baseEnd_5603493 < baseStart_5603493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603499 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 6, 6, 2]
def baseStart_5603499 : Nat := 118140960795 + 5603499 * 2 ^ 59
def prefixEnd_5603499 : Nat := 4983230072969 + 3 ^ 40 * 5603499 * 2
def baseEnd_5603499 : Nat := 2877288333988277018092483

theorem tailTrace_5603499 : CollatzResearch.WordTrace tailWord_5603499 prefixEnd_5603499 2877288333988277018092483 := by
  unfold tailWord_5603499
  simp only [CollatzResearch.WordTrace]
  refine ⟨204376398726487599283533551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136250932484325066189022367 204376398726487599283533551)
  ·
    refine ⟨306564598089731398925300327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204376398726487599283533551 306564598089731398925300327)
    ·
      refine ⟨459846897134597098387950491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306564598089731398925300327 459846897134597098387950491)
      ·
        refine ⟨689770345701895647581925737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459846897134597098387950491 689770345701895647581925737)
        ·
          refine ⟨517327759276421735686444303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 689770345701895647581925737 517327759276421735686444303)
          ·
            refine ⟨775991638914632603529666455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 517327759276421735686444303 775991638914632603529666455)
            ·
              refine ⟨1163987458371948905294499683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 775991638914632603529666455 1163987458371948905294499683)
              ·
                refine ⟨1745981187557923357941749525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1163987458371948905294499683 1745981187557923357941749525)
                ·
                  refine ⟨81842868166777657403519509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1745981187557923357941749525 81842868166777657403519509)
                  ·
                    refine ⟨3836384445317702690789977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81842868166777657403519509 3836384445317702690789977)
                    ·
                      refine ⟨2877288333988277018092483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3836384445317702690789977 2877288333988277018092483)
                      ·
                        rfl

theorem cell23_5603499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 6, 2].length) (baseStart_5603499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603499 prefixEnd_5603499 := by exact prefixLift 5603499
  have htrace : WordTrace (prefixWord ++ tailWord_5603499) baseStart_5603499 baseEnd_5603499 := by
    simpa [prefixWord, tailWord_5603499, baseEnd_5603499] using wordTrace_append hprefix tailTrace_5603499
  have hstable : (prefixWord ++ tailWord_5603499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603499).length < 2 ^ (prefixWord ++ tailWord_5603499).sum := by decide
  have hdescent : baseEnd_5603499 < baseStart_5603499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603576 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 5, 3, 2]
def baseStart_5603576 : Nat := 118140960795 + 5603576 * 2 ^ 59
def prefixEnd_5603576 : Nat := 4983230072969 + 3 ^ 40 * 5603576 * 2
def baseEnd_5603576 : Nat := 2877327871998673216829629

theorem tailTrace_5603576 : CollatzResearch.WordTrace tailWord_5603576 prefixEnd_5603576 2877327871998673216829629 := by
  unfold tailWord_5603576
  simp only [CollatzResearch.WordTrace]
  refine ⟨102189603573604320717043291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136252804764805760956057721 102189603573604320717043291)
  ·
    refine ⟨153284405360406481075564937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102189603573604320717043291 153284405360406481075564937)
    ·
      refine ⟨114963304020304860806673703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153284405360406481075564937 114963304020304860806673703)
      ·
        refine ⟨172444956030457291210010555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114963304020304860806673703 172444956030457291210010555)
        ·
          refine ⟨258667434045685936815015833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172444956030457291210010555 258667434045685936815015833)
          ·
            refine ⟨194000575534264452611261875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258667434045685936815015833 194000575534264452611261875)
            ·
              refine ⟨291000863301396678916892813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194000575534264452611261875 291000863301396678916892813)
              ·
                refine ⟨109125323738023754593834805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 291000863301396678916892813 109125323738023754593834805)
                ·
                  refine ⟨10230499100439726993172013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109125323738023754593834805 10230499100439726993172013)
                  ·
                    refine ⟨3836437162664897622439505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10230499100439726993172013 3836437162664897622439505)
                    ·
                      refine ⟨2877327871998673216829629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3836437162664897622439505 2877327871998673216829629)
                      ·
                        rfl

theorem cell23_5603576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 5, 3, 2].length) (baseStart_5603576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603576 prefixEnd_5603576 := by exact prefixLift 5603576
  have htrace : WordTrace (prefixWord ++ tailWord_5603576) baseStart_5603576 baseEnd_5603576 := by
    simpa [prefixWord, tailWord_5603576, baseEnd_5603576] using wordTrace_append hprefix tailTrace_5603576
  have hstable : (prefixWord ++ tailWord_5603576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603576).length < 2 ^ (prefixWord ++ tailWord_5603576).sum := by decide
  have hdescent : baseEnd_5603576 < baseStart_5603576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603593 : List Nat := [1, 2, 1, 1, 3, 4, 1, 4, 1, 3, 2]
def baseStart_5603593 : Nat := 118140960795 + 5603593 * 2 ^ 59
def prefixEnd_5603593 : Nat := 4983230072969 + 3 ^ 40 * 5603593 * 2
def baseEnd_5603593 : Nat := 2877336601169799650317051

theorem tailTrace_5603593 : CollatzResearch.WordTrace tailWord_5603593 prefixEnd_5603593 2877336601169799650317051 := by
  unfold tailWord_5603593
  simp only [CollatzResearch.WordTrace]
  refine ⟨204379827188147053337455433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136253218125431368891636955 204379827188147053337455433)
  ·
    refine ⟨153284870391110290003091575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204379827188147053337455433 153284870391110290003091575)
    ·
      refine ⟨229927305586665435004637363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153284870391110290003091575 229927305586665435004637363)
      ·
        refine ⟨344890958379998152506956045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229927305586665435004637363 344890958379998152506956045)
        ·
          refine ⟨129334109392499307190108517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 344890958379998152506956045 129334109392499307190108517)
          ·
            refine ⟨24250145511093620098145347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129334109392499307190108517 24250145511093620098145347)
            ·
              refine ⟨36375218266640430147218021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24250145511093620098145347 36375218266640430147218021)
              ·
                refine ⟨6820353424995080652603379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36375218266640430147218021 6820353424995080652603379)
                ·
                  refine ⟨10230530137492620978905069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6820353424995080652603379 10230530137492620978905069)
                  ·
                    refine ⟨3836448801559732867089401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10230530137492620978905069 3836448801559732867089401)
                    ·
                      refine ⟨2877336601169799650317051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3836448801559732867089401 2877336601169799650317051)
                      ·
                        rfl

theorem cell23_5603593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 3, 2].length) (baseStart_5603593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603593 prefixEnd_5603593 := by exact prefixLift 5603593
  have htrace : WordTrace (prefixWord ++ tailWord_5603593) baseStart_5603593 baseEnd_5603593 := by
    simpa [prefixWord, tailWord_5603593, baseEnd_5603593] using wordTrace_append hprefix tailTrace_5603593
  have hstable : (prefixWord ++ tailWord_5603593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603593).length < 2 ^ (prefixWord ++ tailWord_5603593).sum := by decide
  have hdescent : baseEnd_5603593 < baseStart_5603593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603634 : List Nat := [3, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3]
def baseStart_5603634 : Nat := 118140960795 + 5603634 * 2 ^ 59
def prefixEnd_5603634 : Nat := 4983230072969 + 3 ^ 40 * 5603634 * 2
def baseEnd_5603634 : Nat := 2877357653876633989904363

theorem tailTrace_5603634 : CollatzResearch.WordTrace tailWord_5603634 prefixEnd_5603634 2877357653876633989904363 := by
  unfold tailWord_5603634
  simp only [CollatzResearch.WordTrace]
  refine ⟨51095330645249629334924489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136254215053999011559798637 51095330645249629334924489)
  ·
    refine ⟨38321497983937222001193367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51095330645249629334924489 38321497983937222001193367)
    ·
      refine ⟨57482246975905833001790051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38321497983937222001193367 57482246975905833001790051)
      ·
        refine ⟨86223370463858749502685077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57482246975905833001790051 86223370463858749502685077)
        ·
          refine ⟨4041720490493378882938363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 86223370463858749502685077 4041720490493378882938363)
          ·
            refine ⟨6062580735740068324407545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4041720490493378882938363 6062580735740068324407545)
            ·
              refine ⟨4546935551805051243305659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6062580735740068324407545 4546935551805051243305659)
              ·
                refine ⟨6820403327707576864958489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4546935551805051243305659 6820403327707576864958489)
                ·
                  refine ⟨5115302495780682648718867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6820403327707576864958489 5115302495780682648718867)
                  ·
                    refine ⟨7672953743671023973078301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5115302495780682648718867 7672953743671023973078301)
                    ·
                      refine ⟨2877357653876633989904363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7672953743671023973078301 2877357653876633989904363)
                      ·
                        rfl

theorem cell23_5603634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3].length) (baseStart_5603634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603634 prefixEnd_5603634 := by exact prefixLift 5603634
  have htrace : WordTrace (prefixWord ++ tailWord_5603634) baseStart_5603634 baseEnd_5603634 := by
    simpa [prefixWord, tailWord_5603634, baseEnd_5603634] using wordTrace_append hprefix tailTrace_5603634
  have hstable : (prefixWord ++ tailWord_5603634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603634).length < 2 ^ (prefixWord ++ tailWord_5603634).sum := by decide
  have hdescent : baseEnd_5603634 < baseStart_5603634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603699 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 5]
def baseStart_5603699 : Nat := 118140960795 + 5603699 * 2 ^ 59
def prefixEnd_5603699 : Nat := 4983230072969 + 3 ^ 40 * 5603699 * 2
def baseEnd_5603699 : Nat := 2877391030119176235591563

theorem tailTrace_5603699 : CollatzResearch.WordTrace tailWord_5603699 prefixEnd_5603699 2877391030119176235591563 := by
  unfold tailWord_5603699
  simp only [CollatzResearch.WordTrace]
  refine ⟨204383693325763033440814151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136255795550508688960542767 204383693325763033440814151)
  ·
    refine ⟨306575539988644550161221227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204383693325763033440814151 306575539988644550161221227)
    ·
      refine ⟨459863309982966825241831841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306575539988644550161221227 459863309982966825241831841)
      ·
        refine ⟨344897482487225118931373881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 459863309982966825241831841 344897482487225118931373881)
        ·
          refine ⟨258673111865418839198530411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344897482487225118931373881 258673111865418839198530411)
          ·
            refine ⟨388009667798128258797795617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258673111865418839198530411 388009667798128258797795617)
            ·
              refine ⟨291007250848596194098346713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 388009667798128258797795617 291007250848596194098346713)
              ·
                refine ⟨218255438136447145573760035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291007250848596194098346713 218255438136447145573760035)
                ·
                  refine ⟨327383157204670718360640053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218255438136447145573760035 327383157204670718360640053)
                  ·
                    refine ⟨30692170987937879846310005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 327383157204670718360640053 30692170987937879846310005)
                    ·
                      refine ⟨2877391030119176235591563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30692170987937879846310005 2877391030119176235591563)
                      ·
                        rfl

theorem cell23_5603699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 5].length) (baseStart_5603699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603699 prefixEnd_5603699 := by exact prefixLift 5603699
  have htrace : WordTrace (prefixWord ++ tailWord_5603699) baseStart_5603699 baseEnd_5603699 := by
    simpa [prefixWord, tailWord_5603699, baseEnd_5603699] using wordTrace_append hprefix tailTrace_5603699
  have hstable : (prefixWord ++ tailWord_5603699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603699).length < 2 ^ (prefixWord ++ tailWord_5603699).sum := by decide
  have hdescent : baseEnd_5603699 < baseStart_5603699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603713 : List Nat := [1, 2, 4, 3, 1, 2, 1, 1, 1, 3, 4]
def baseStart_5603713 : Nat := 118140960795 + 5603713 * 2 ^ 59
def prefixEnd_5603713 : Nat := 4983230072969 + 3 ^ 40 * 5603713 * 2
def baseEnd_5603713 : Nat := 2877398218848339180816499

theorem tailTrace_5603713 : CollatzResearch.WordTrace tailWord_5603713 prefixEnd_5603713 2877398218848339180816499 := by
  unfold tailWord_5603713
  simp only [CollatzResearch.WordTrace]
  refine ⟨204384203947712313831823793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136256135965141542554549195 204384203947712313831823793)
  ·
    refine ⟨153288152960784235373867845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204384203947712313831823793 153288152960784235373867845)
    ·
      refine ⟨28741528680147044132600221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153288152960784235373867845 28741528680147044132600221)
      ·
        refine ⟨10778073255055141549725083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28741528680147044132600221 10778073255055141549725083)
        ·
          refine ⟨16167109882582712324587625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10778073255055141549725083 16167109882582712324587625)
          ·
            refine ⟨12125332411937034243440719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16167109882582712324587625 12125332411937034243440719)
            ·
              refine ⟨18187998617905551365161079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12125332411937034243440719 18187998617905551365161079)
              ·
                refine ⟨27281997926858327047741619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18187998617905551365161079 27281997926858327047741619)
                ·
                  refine ⟨40922996890287490571612429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27281997926858327047741619 40922996890287490571612429)
                  ·
                    refine ⟨15346123833857808964354661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40922996890287490571612429 15346123833857808964354661)
                    ·
                      refine ⟨2877398218848339180816499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15346123833857808964354661 2877398218848339180816499)
                      ·
                        rfl

theorem cell23_5603713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_5603713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603713 prefixEnd_5603713 := by exact prefixLift 5603713
  have htrace : WordTrace (prefixWord ++ tailWord_5603713) baseStart_5603713 baseEnd_5603713 := by
    simpa [prefixWord, tailWord_5603713, baseEnd_5603713] using wordTrace_append hprefix tailTrace_5603713
  have hstable : (prefixWord ++ tailWord_5603713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603713).length < 2 ^ (prefixWord ++ tailWord_5603713).sum := by decide
  have hdescent : baseEnd_5603713 < baseStart_5603713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603783 : List Nat := [1, 1, 4, 1, 1, 4, 2, 3, 1, 5]
def baseStart_5603783 : Nat := 118140960795 + 5603783 * 2 ^ 59
def prefixEnd_5603783 : Nat := 4983230072969 + 3 ^ 40 * 5603783 * 2
def baseEnd_5603783 : Nat := 959144720831384635647059

theorem tailTrace_5603783 : CollatzResearch.WordTrace tailWord_5603783 prefixEnd_5603783 959144720831384635647059 := by
  unfold tailWord_5603783
  simp only [CollatzResearch.WordTrace]
  refine ⟨204386757057458715786872003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136257838038305810524581335 204386757057458715786872003)
  ·
    refine ⟨306580135586188073680308005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204386757057458715786872003 306580135586188073680308005)
    ·
      refine ⟨57483775422410263815057751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 306580135586188073680308005 57483775422410263815057751)
      ·
        refine ⟨86225663133615395722586627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57483775422410263815057751 86225663133615395722586627)
        ·
          refine ⟨129338494700423093583879941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86225663133615395722586627 129338494700423093583879941)
          ·
            refine ⟨24250967756329330046977489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129338494700423093583879941 24250967756329330046977489)
            ·
              refine ⟨18188225817246997535233117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24250967756329330046977489 18188225817246997535233117)
              ·
                refine ⟨6820584681467624075712419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18188225817246997535233117 6820584681467624075712419)
                ·
                  refine ⟨10230877022201436113568629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6820584681467624075712419 10230877022201436113568629)
                  ·
                    refine ⟨959144720831384635647059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10230877022201436113568629 959144720831384635647059)
                    ·
                      rfl

theorem cell23_5603783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_5603783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603783 prefixEnd_5603783 := by exact prefixLift 5603783
  have htrace : WordTrace (prefixWord ++ tailWord_5603783) baseStart_5603783 baseEnd_5603783 := by
    simpa [prefixWord, tailWord_5603783, baseEnd_5603783] using wordTrace_append hprefix tailTrace_5603783
  have hstable : (prefixWord ++ tailWord_5603783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603783).length < 2 ^ (prefixWord ++ tailWord_5603783).sum := by decide
  have hdescent : baseEnd_5603783 < baseStart_5603783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603797 : List Nat := [1, 3, 2, 3, 1, 4, 1, 1, 3, 1, 3]
def baseStart_5603797 : Nat := 118140960795 + 5603797 * 2 ^ 59
def prefixEnd_5603797 : Nat := 4983230072969 + 3 ^ 40 * 5603797 * 2
def baseEnd_5603797 : Nat := 2877441351223316852166113

theorem tailTrace_5603797 : CollatzResearch.WordTrace tailWord_5603797 prefixEnd_5603797 2877441351223316852166113 := by
  unfold tailWord_5603797
  simp only [CollatzResearch.WordTrace]
  refine ⟨204387267679407996177881645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136258178452938664118587763 204387267679407996177881645)
  ·
    refine ⟨76645225379777998566705617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204387267679407996177881645 76645225379777998566705617)
    ·
      refine ⟨57483919034833498925029213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76645225379777998566705617 57483919034833498925029213)
      ·
        refine ⟨21556469638062562096885955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57483919034833498925029213 21556469638062562096885955)
        ·
          refine ⟨32334704457093843145328933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21556469638062562096885955 32334704457093843145328933)
          ·
            refine ⟨6062757085705095589749175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32334704457093843145328933 6062757085705095589749175)
            ·
              refine ⟨9094135628557643384623763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6062757085705095589749175 9094135628557643384623763)
              ·
                refine ⟨13641203442836465076935645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9094135628557643384623763 13641203442836465076935645)
                ·
                  refine ⟨5115451291063674403850867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13641203442836465076935645 5115451291063674403850867)
                  ·
                    refine ⟨7673176936595511605776301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5115451291063674403850867 7673176936595511605776301)
                    ·
                      refine ⟨2877441351223316852166113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7673176936595511605776301 2877441351223316852166113)
                      ·
                        rfl

theorem cell23_5603797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_5603797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603797 prefixEnd_5603797 := by exact prefixLift 5603797
  have htrace : WordTrace (prefixWord ++ tailWord_5603797) baseStart_5603797 baseEnd_5603797 := by
    simpa [prefixWord, tailWord_5603797, baseEnd_5603797] using wordTrace_append hprefix tailTrace_5603797
  have hstable : (prefixWord ++ tailWord_5603797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603797).length < 2 ^ (prefixWord ++ tailWord_5603797).sum := by decide
  have hdescent : baseEnd_5603797 < baseStart_5603797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603820 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 5, 2, 2]
def baseStart_5603820 : Nat := 118140960795 + 5603820 * 2 ^ 59
def prefixEnd_5603820 : Nat := 4983230072969 + 3 ^ 40 * 5603820 * 2
def baseEnd_5603820 : Nat := 2877453161278370262178507

theorem tailTrace_5603820 : CollatzResearch.WordTrace tailWord_5603820 prefixEnd_5603820 2877453161278370262178507 := by
  unfold tailWord_5603820
  simp only [CollatzResearch.WordTrace]
  refine ⟨102194053279162335552984457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136258737705549780737312609 102194053279162335552984457)
  ·
    refine ⟨76645539959371751664738343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102194053279162335552984457 76645539959371751664738343)
    ·
      refine ⟨114968309939057627497107515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76645539959371751664738343 114968309939057627497107515)
      ·
        refine ⟨172452464908586441245661273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114968309939057627497107515 172452464908586441245661273)
        ·
          refine ⟨129339348681439830934245955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172452464908586441245661273 129339348681439830934245955)
          ·
            refine ⟨194009023022159746401368933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129339348681439830934245955 194009023022159746401368933)
            ·
              refine ⟨36376691816654952450256675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 194009023022159746401368933 36376691816654952450256675)
              ·
                refine ⟨54565037724982428675385013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36376691816654952450256675 54565037724982428675385013)
                ·
                  refine ⟨5115472286717102688317345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54565037724982428675385013 5115472286717102688317345)
                  ·
                    refine ⟨3836604215037827016238009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5115472286717102688317345 3836604215037827016238009)
                    ·
                      refine ⟨2877453161278370262178507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3836604215037827016238009 2877453161278370262178507)
                      ·
                        rfl

theorem cell23_5603820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 2, 2].length) (baseStart_5603820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603820 prefixEnd_5603820 := by exact prefixLift 5603820
  have htrace : WordTrace (prefixWord ++ tailWord_5603820) baseStart_5603820 baseEnd_5603820 := by
    simpa [prefixWord, tailWord_5603820, baseEnd_5603820] using wordTrace_append hprefix tailTrace_5603820
  have hstable : (prefixWord ++ tailWord_5603820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603820).length < 2 ^ (prefixWord ++ tailWord_5603820).sum := by decide
  have hdescent : baseEnd_5603820 < baseStart_5603820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603847 : List Nat := [1, 1, 4, 3, 3, 1, 2, 2, 2, 4]
def baseStart_5603847 : Nat := 118140960795 + 5603847 * 2 ^ 59
def prefixEnd_5603847 : Nat := 4983230072969 + 3 ^ 40 * 5603847 * 2
def baseEnd_5603847 : Nat := 959155675085347218846961

theorem tailTrace_5603847 : CollatzResearch.WordTrace tailWord_5603847 prefixEnd_5603847 959155675085347218846961 := by
  unfold tailWord_5603847
  simp only [CollatzResearch.WordTrace]
  refine ⟨204389091329226854717201795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136259394219484569811467863 204389091329226854717201795)
  ·
    refine ⟨306583636993840282075802693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204389091329226854717201795 306583636993840282075802693)
    ·
      refine ⟨57484431936345052889213005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 306583636993840282075802693 57484431936345052889213005)
      ·
        refine ⟨21556661976129394833454877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57484431936345052889213005 21556661976129394833454877)
        ·
          refine ⟨8083748241048523062545579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21556661976129394833454877 8083748241048523062545579)
          ·
            refine ⟨12125622361572784593818369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8083748241048523062545579 12125622361572784593818369)
            ·
              refine ⟨9094216771179588445363777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12125622361572784593818369 9094216771179588445363777)
              ·
                refine ⟨6820662578384691334022833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9094216771179588445363777 6820662578384691334022833)
                ·
                  refine ⟨5115496933788518500517125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6820662578384691334022833 5115496933788518500517125)
                  ·
                    refine ⟨959155675085347218846961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5115496933788518500517125 959155675085347218846961)
                    ·
                      rfl

theorem cell23_5603847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_5603847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603847 prefixEnd_5603847 := by exact prefixLift 5603847
  have htrace : WordTrace (prefixWord ++ tailWord_5603847) baseStart_5603847 baseEnd_5603847 := by
    simpa [prefixWord, tailWord_5603847, baseEnd_5603847] using wordTrace_append hprefix tailTrace_5603847
  have hstable : (prefixWord ++ tailWord_5603847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603847).length < 2 ^ (prefixWord ++ tailWord_5603847).sum := by decide
  have hdescent : baseEnd_5603847 < baseStart_5603847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603860 : List Nat := [2, 4, 3, 1, 1, 1, 3, 8]
def baseStart_5603860 : Nat := 118140960795 + 5603860 * 2 ^ 59
def prefixEnd_5603860 : Nat := 4983230072969 + 3 ^ 40 * 5603860 * 2
def baseEnd_5603860 : Nat := 106573100018687040951049

theorem tailTrace_5603860 : CollatzResearch.WordTrace tailWord_5603860 prefixEnd_5603860 106573100018687040951049 := by
  unfold tailWord_5603860
  simp only [CollatzResearch.WordTrace]
  refine ⟨102194782739089878968712517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136259710318786505291616689 102194782739089878968712517)
  ·
    refine ⟨19161521763579352306633597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102194782739089878968712517 19161521763579352306633597)
    ·
      refine ⟨7185570661342257114987599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19161521763579352306633597 7185570661342257114987599)
      ·
        refine ⟨10778355992013385672481399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7185570661342257114987599 10778355992013385672481399)
        ·
          refine ⟨16167533988020078508722099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10778355992013385672481399 16167533988020078508722099)
          ·
            refine ⟨24251300982030117763083149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16167533988020078508722099 24251300982030117763083149)
            ·
              refine ⟨9094237868261294161156181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24251300982030117763083149 9094237868261294161156181)
              ·
                refine ⟨106573100018687040951049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9094237868261294161156181 106573100018687040951049)
                ·
                  rfl

theorem cell23_5603860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 8].length) (baseStart_5603860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603860 prefixEnd_5603860 := by exact prefixLift 5603860
  have htrace : WordTrace (prefixWord ++ tailWord_5603860) baseStart_5603860 baseEnd_5603860 := by
    simpa [prefixWord, tailWord_5603860, baseEnd_5603860] using wordTrace_append hprefix tailTrace_5603860
  have hstable : (prefixWord ++ tailWord_5603860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603860).length < 2 ^ (prefixWord ++ tailWord_5603860).sum := by decide
  have hdescent : baseEnd_5603860 < baseStart_5603860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603897 : List Nat := [1, 2, 1, 5, 1, 1, 3, 3, 1, 3, 2]
def baseStart_5603897 : Nat := 118140960795 + 5603897 * 2 ^ 59
def prefixEnd_5603897 : Nat := 4983230072969 + 3 ^ 40 * 5603897 * 2
def baseEnd_5603897 : Nat := 2877492699288766460915653

theorem tailTrace_5603897 : CollatzResearch.WordTrace tailWord_5603897 prefixEnd_5603897 2877492699288766460915653 := by
  unfold tailWord_5603897
  simp only [CollatzResearch.WordTrace]
  refine ⟨204390914979045713256521945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136260609986030475504347963 204390914979045713256521945)
  ·
    refine ⟨153293186234284284942391459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204390914979045713256521945 153293186234284284942391459)
    ·
      refine ⟨229939779351426427413587189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153293186234284284942391459 229939779351426427413587189)
      ·
        refine ⟨21556854314196227570023799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 229939779351426427413587189 21556854314196227570023799)
        ·
          refine ⟨32335281471294341355035699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21556854314196227570023799 32335281471294341355035699)
          ·
            refine ⟨48502922206941512032553549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32335281471294341355035699 48502922206941512032553549)
            ·
              refine ⟨18188595827603067012207581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48502922206941512032553549 18188595827603067012207581)
              ·
                refine ⟨6820723435351150129577843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18188595827603067012207581 6820723435351150129577843)
                ·
                  refine ⟨10231085153026725194366765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6820723435351150129577843 10231085153026725194366765)
                  ·
                    refine ⟨3836656932385021947887537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10231085153026725194366765 3836656932385021947887537)
                    ·
                      refine ⟨2877492699288766460915653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3836656932385021947887537 2877492699288766460915653)
                      ·
                        rfl

theorem cell23_5603897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_5603897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603897 prefixEnd_5603897 := by exact prefixLift 5603897
  have htrace : WordTrace (prefixWord ++ tailWord_5603897) baseStart_5603897 baseEnd_5603897 := by
    simpa [prefixWord, tailWord_5603897, baseEnd_5603897] using wordTrace_append hprefix tailTrace_5603897
  have hstable : (prefixWord ++ tailWord_5603897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603897).length < 2 ^ (prefixWord ++ tailWord_5603897).sum := by decide
  have hdescent : baseEnd_5603897 < baseStart_5603897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603973 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 1, 1, 7]
def baseStart_5603973 : Nat := 118140960795 + 5603973 * 2 ^ 59
def prefixEnd_5603973 : Nat := 4983230072969 + 3 ^ 40 * 5603973 * 2
def baseEnd_5603973 : Nat := 2877531723818508163565303

theorem tailTrace_5603973 : CollatzResearch.WordTrace tailWord_5603973 prefixEnd_5603973 2877531723818508163565303 := by
  unfold tailWord_5603973
  simp only [CollatzResearch.WordTrace]
  refine ⟨204393686926770378236288573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136262457951180252157525715 204393686926770378236288573)
  ·
    refine ⟨76647632597538891838608215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204393686926770378236288573 76647632597538891838608215)
    ·
      refine ⟨114971448896308337757912323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76647632597538891838608215 114971448896308337757912323)
      ·
        refine ⟨172457173344462506636868485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114971448896308337757912323 172457173344462506636868485)
        ·
          refine ⟨32335720002086719994412841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172457173344462506636868485 32335720002086719994412841)
          ·
            refine ⟨24251790001565039995809631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32335720002086719994412841 24251790001565039995809631)
            ·
              refine ⟨36377685002347559993714447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24251790001565039995809631 36377685002347559993714447)
              ·
                refine ⟨54566527503521339990571671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36377685002347559993714447 54566527503521339990571671)
                ·
                  refine ⟨81849791255282009985857507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54566527503521339990571671 81849791255282009985857507)
                  ·
                    refine ⟨122774686882923014978786261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81849791255282009985857507 122774686882923014978786261)
                    ·
                      refine ⟨2877531723818508163565303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 122774686882923014978786261 2877531723818508163565303)
                      ·
                        rfl

theorem cell23_5603973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_5603973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603973 prefixEnd_5603973 := by exact prefixLift 5603973
  have htrace : WordTrace (prefixWord ++ tailWord_5603973) baseStart_5603973 baseEnd_5603973 := by
    simpa [prefixWord, tailWord_5603973, baseEnd_5603973] using wordTrace_append hprefix tailTrace_5603973
  have hstable : (prefixWord ++ tailWord_5603973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603973).length < 2 ^ (prefixWord ++ tailWord_5603973).sum := by decide
  have hdescent : baseEnd_5603973 < baseStart_5603973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5603978 : List Nat := [3, 1, 2, 3, 3, 2, 2, 1, 2, 2, 2]
def baseStart_5603978 : Nat := 118140960795 + 5603978 * 2 ^ 59
def prefixEnd_5603978 : Nat := 4983230072969 + 3 ^ 40 * 5603978 * 2
def baseEnd_5603978 : Nat := 2877534291221780644002781

theorem tailTrace_5603978 : CollatzResearch.WordTrace tailWord_5603978 prefixEnd_5603978 2877534291221780644002781 := by
  unfold tailWord_5603978
  simp only [CollatzResearch.WordTrace]
  refine ⟨51098467322938066022555147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136262579527834842726813725 51098467322938066022555147)
  ·
    refine ⟨76647700984407099033832721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51098467322938066022555147 76647700984407099033832721)
    ·
      refine ⟨57485775738305324275374541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76647700984407099033832721 57485775738305324275374541)
      ·
        refine ⟨21557165901864496603265453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57485775738305324275374541 21557165901864496603265453)
        ·
          refine ⟨8083937213199186226224545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21557165901864496603265453 8083937213199186226224545)
          ·
            refine ⟨6062952909899389669668409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8083937213199186226224545 6062952909899389669668409)
            ·
              refine ⟨4547214682424542252251307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6062952909899389669668409 4547214682424542252251307)
              ·
                refine ⟨6820822023636813378376961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4547214682424542252251307 6820822023636813378376961)
                ·
                  refine ⟨5115616517727610033782721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6820822023636813378376961 5115616517727610033782721)
                  ·
                    refine ⟨3836712388295707525337041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5115616517727610033782721 3836712388295707525337041)
                    ·
                      refine ⟨2877534291221780644002781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3836712388295707525337041 2877534291221780644002781)
                      ·
                        rfl

theorem cell23_5603978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_5603978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5603978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5603978 prefixEnd_5603978 := by exact prefixLift 5603978
  have htrace : WordTrace (prefixWord ++ tailWord_5603978) baseStart_5603978 baseEnd_5603978 := by
    simpa [prefixWord, tailWord_5603978, baseEnd_5603978] using wordTrace_append hprefix tailTrace_5603978
  have hstable : (prefixWord ++ tailWord_5603978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5603978).length < 2 ^ (prefixWord ++ tailWord_5603978).sum := by decide
  have hdescent : baseEnd_5603978 < baseStart_5603978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5603978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604040 : List Nat := [2, 1, 3, 1, 2, 3, 2, 3, 6]
def baseStart_5604040 : Nat := 118140960795 + 5604040 * 2 ^ 59
def prefixEnd_5604040 : Nat := 4983230072969 + 3 ^ 40 * 5604040 * 2
def baseEnd_5604040 : Nat := 319729569669151044603055

theorem tailTrace_5604040 : CollatzResearch.WordTrace tailWord_5604040 prefixEnd_5604040 319729569669151044603055 := by
  unfold tailWord_5604040
  simp only [CollatzResearch.WordTrace]
  refine ⟨102198065308763824339488787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136264087078351765785985049 102198065308763824339488787)
  ·
    refine ⟨153297097963145736509233181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102198065308763824339488787 153297097963145736509233181)
    ·
      refine ⟨57486411736179651190962443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153297097963145736509233181 57486411736179651190962443)
      ·
        refine ⟨86229617604269476786443665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57486411736179651190962443 86229617604269476786443665)
        ·
          refine ⟨64672213203202107589832749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86229617604269476786443665 64672213203202107589832749)
          ·
            refine ⟨24252079951200790346187281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64672213203202107589832749 24252079951200790346187281)
            ·
              refine ⟨18189059963400592759640461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24252079951200790346187281 18189059963400592759640461)
              ·
                refine ⟨6820897486275222284865173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18189059963400592759640461 6820897486275222284865173)
                ·
                  refine ⟨319729569669151044603055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6820897486275222284865173 319729569669151044603055)
                  ·
                    rfl

theorem cell23_5604040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 6].length) (baseStart_5604040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604040 prefixEnd_5604040 := by exact prefixLift 5604040
  have htrace : WordTrace (prefixWord ++ tailWord_5604040) baseStart_5604040 baseEnd_5604040 := by
    simpa [prefixWord, tailWord_5604040, baseEnd_5604040] using wordTrace_append hprefix tailTrace_5604040
  have hstable : (prefixWord ++ tailWord_5604040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604040).length < 2 ^ (prefixWord ++ tailWord_5604040).sum := by decide
  have hdescent : baseEnd_5604040 < baseStart_5604040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604090 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 5, 1, 4]
def baseStart_5604090 : Nat := 118140960795 + 5604090 * 2 ^ 59
def prefixEnd_5604090 : Nat := 4983230072969 + 3 ^ 40 * 5604090 * 2
def baseEnd_5604090 : Nat := 2877591801055084205802265

theorem tailTrace_5604090 : CollatzResearch.WordTrace tailWord_5604090 prefixEnd_5604090 2877591801055084205802265 := by
  unfold tailWord_5604090
  simp only [CollatzResearch.WordTrace]
  refine ⟨51099488566836626804574431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136265302844897671478865149 51099488566836626804574431)
  ·
    refine ⟨76649232850254940206861647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51099488566836626804574431 76649232850254940206861647)
    ·
      refine ⟨114973849275382410310292471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76649232850254940206861647 114973849275382410310292471)
      ·
        refine ⟨172460773913073615465438707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114973849275382410310292471 172460773913073615465438707)
        ·
          refine ⟨258691160869610423198158061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172460773913073615465438707 258691160869610423198158061)
          ·
            refine ⟨97009185326103908699309273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 258691160869610423198158061 97009185326103908699309273)
            ·
              refine ⟨72756888994577931524481955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97009185326103908699309273 72756888994577931524481955)
              ·
                refine ⟨109135333491866897286722933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72756888994577931524481955 109135333491866897286722933)
                ·
                  refine ⟨10231437514862521620630275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109135333491866897286722933 10231437514862521620630275)
                  ·
                    refine ⟨15347156272293782430945413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10231437514862521620630275 15347156272293782430945413)
                    ·
                      refine ⟨2877591801055084205802265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15347156272293782430945413 2877591801055084205802265)
                      ·
                        rfl

theorem cell23_5604090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_5604090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604090 prefixEnd_5604090 := by exact prefixLift 5604090
  have htrace : WordTrace (prefixWord ++ tailWord_5604090) baseStart_5604090 baseEnd_5604090 := by
    simpa [prefixWord, tailWord_5604090, baseEnd_5604090] using wordTrace_append hprefix tailTrace_5604090
  have hstable : (prefixWord ++ tailWord_5604090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604090).length < 2 ^ (prefixWord ++ tailWord_5604090).sum := by decide
  have hdescent : baseEnd_5604090 < baseStart_5604090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604094 : List Nat := [4, 2, 2, 1, 2, 1, 1, 2, 1, 5, 2]
def baseStart_5604094 : Nat := 118140960795 + 5604094 * 2 ^ 59
def prefixEnd_5604094 : Nat := 4983230072969 + 3 ^ 40 * 5604094 * 2
def baseEnd_5604094 : Nat := 2877593854977702190152247

theorem tailTrace_5604094 : CollatzResearch.WordTrace tailWord_5604094 prefixEnd_5604094 2877593854977702190152247 := by
  unfold tailWord_5604094
  simp only [CollatzResearch.WordTrace]
  refine ⟨25549762519916501987680417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136265400106221343934295557 25549762519916501987680417)
  ·
    refine ⟨19162321889937376490760313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25549762519916501987680417 19162321889937376490760313)
    ·
      refine ⟨14371741417453032368070235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19162321889937376490760313 14371741417453032368070235)
      ·
        refine ⟨21557612126179548552105353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14371741417453032368070235 21557612126179548552105353)
        ·
          refine ⟨16168209094634661414079015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21557612126179548552105353 16168209094634661414079015)
          ·
            refine ⟨24252313641951992121118523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16168209094634661414079015 24252313641951992121118523)
            ·
              refine ⟨36378470462927988181677785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24252313641951992121118523 36378470462927988181677785)
              ·
                refine ⟨27283852847195991136258339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36378470462927988181677785 27283852847195991136258339)
                ·
                  refine ⟨40925779270793986704387509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27283852847195991136258339 40925779270793986704387509)
                  ·
                    refine ⟨3836791806636936253536329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40925779270793986704387509 3836791806636936253536329)
                    ·
                      refine ⟨2877593854977702190152247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3836791806636936253536329 2877593854977702190152247)
                      ·
                        rfl

theorem cell23_5604094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_5604094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604094 prefixEnd_5604094 := by exact prefixLift 5604094
  have htrace : WordTrace (prefixWord ++ tailWord_5604094) baseStart_5604094 baseEnd_5604094 := by
    simpa [prefixWord, tailWord_5604094, baseEnd_5604094] using wordTrace_append hprefix tailTrace_5604094
  have hstable : (prefixWord ++ tailWord_5604094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604094).length < 2 ^ (prefixWord ++ tailWord_5604094).sum := by decide
  have hdescent : baseEnd_5604094 < baseStart_5604094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604110 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5]
def baseStart_5604110 : Nat := 118140960795 + 5604110 * 2 ^ 59
def prefixEnd_5604110 : Nat := 4983230072969 + 3 ^ 40 * 5604110 * 2
def baseEnd_5604110 : Nat := 2877602070668174127552173

theorem tailTrace_5604110 : CollatzResearch.WordTrace tailWord_5604110 prefixEnd_5604110 2877602070668174127552173 := by
  unfold tailWord_5604110
  simp only [CollatzResearch.WordTrace]
  refine ⟨25549835465909256329253223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136265789151516033756017189 25549835465909256329253223)
  ·
    refine ⟨38324753198863884493879835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25549835465909256329253223 38324753198863884493879835)
    ·
      refine ⟨57487129798295826740819753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38324753198863884493879835 57487129798295826740819753)
      ·
        refine ⟨43115347348721870055614815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57487129798295826740819753 43115347348721870055614815)
        ·
          refine ⟨64673021023082805083422223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43115347348721870055614815 64673021023082805083422223)
          ·
            refine ⟨97009531534624207625133335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64673021023082805083422223 97009531534624207625133335)
            ·
              refine ⟨145514297301936311437700003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97009531534624207625133335 145514297301936311437700003)
              ·
                refine ⟨218271445952904467156550005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145514297301936311437700003 218271445952904467156550005)
                ·
                  refine ⟨20462948058084793795926563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 218271445952904467156550005 20462948058084793795926563)
                  ·
                    refine ⟨30694422087127190693889845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20462948058084793795926563 30694422087127190693889845)
                    ·
                      refine ⟨2877602070668174127552173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30694422087127190693889845 2877602070668174127552173)
                      ·
                        rfl

theorem cell23_5604110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_5604110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604110 prefixEnd_5604110 := by exact prefixLift 5604110
  have htrace : WordTrace (prefixWord ++ tailWord_5604110) baseStart_5604110 baseEnd_5604110 := by
    simpa [prefixWord, tailWord_5604110, baseEnd_5604110] using wordTrace_append hprefix tailTrace_5604110
  have hstable : (prefixWord ++ tailWord_5604110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604110).length < 2 ^ (prefixWord ++ tailWord_5604110).sum := by decide
  have hdescent : baseEnd_5604110 < baseStart_5604110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604120 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 3, 2, 4]
def baseStart_5604120 : Nat := 118140960795 + 5604120 * 2 ^ 59
def prefixEnd_5604120 : Nat := 4983230072969 + 3 ^ 40 * 5604120 * 2
def baseEnd_5604120 : Nat := 2877607205474719088427127

theorem tailTrace_5604120 : CollatzResearch.WordTrace tailWord_5604120 prefixEnd_5604120 2877607205474719088427127 := by
  unfold tailWord_5604120
  simp only [CollatzResearch.WordTrace]
  refine ⟨102199524228618911170944907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136266032304825214894593209 102199524228618911170944907)
  ·
    refine ⟨153299286342928366756417361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102199524228618911170944907 153299286342928366756417361)
    ·
      refine ⟨114974464757196275067313021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153299286342928366756417361 114974464757196275067313021)
      ·
        refine ⟨43115424283948603150242383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114974464757196275067313021 43115424283948603150242383)
        ·
          refine ⟨64673136425922904725363575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43115424283948603150242383 64673136425922904725363575)
          ·
            refine ⟨97009704638884357088045363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64673136425922904725363575 97009704638884357088045363)
            ·
              refine ⟨145514556958326535632068045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97009704638884357088045363 145514556958326535632068045)
              ·
                refine ⟨54567958859372450862025517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145514556958326535632068045 54567958859372450862025517)
                ·
                  refine ⟨20462984572264669073259569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54567958859372450862025517 20462984572264669073259569)
                  ·
                    refine ⟨15347238429198501804944677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20462984572264669073259569 15347238429198501804944677)
                    ·
                      refine ⟨2877607205474719088427127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15347238429198501804944677 2877607205474719088427127)
                      ·
                        rfl

theorem cell23_5604120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_5604120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604120 prefixEnd_5604120 := by exact prefixLift 5604120
  have htrace : WordTrace (prefixWord ++ tailWord_5604120) baseStart_5604120 baseEnd_5604120 := by
    simpa [prefixWord, tailWord_5604120, baseEnd_5604120] using wordTrace_append hprefix tailTrace_5604120
  have hstable : (prefixWord ++ tailWord_5604120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604120).length < 2 ^ (prefixWord ++ tailWord_5604120).sum := by decide
  have hdescent : baseEnd_5604120 < baseStart_5604120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604127 : List Nat := [1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 5]
def baseStart_5604127 : Nat := 118140960795 + 5604127 * 2 ^ 59
def prefixEnd_5604127 : Nat := 4983230072969 + 3 ^ 40 * 5604127 * 2
def baseEnd_5604127 : Nat := 2877610799839300561039595

theorem tailTrace_5604127 : CollatzResearch.WordTrace tailWord_5604127 prefixEnd_5604127 2877610799839300561039595 := by
  unfold tailWord_5604127
  simp only [CollatzResearch.WordTrace]
  refine ⟨204399303768212462537394635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136266202512141641691596423 204399303768212462537394635)
  ·
    refine ⟨306598955652318693806091953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204399303768212462537394635 306598955652318693806091953)
    ·
      refine ⟨229949216739239020354568965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306598955652318693806091953 229949216739239020354568965)
      ·
        refine ⟨43115478138607316316481681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 229949216739239020354568965 43115478138607316316481681)
        ·
          refine ⟨32336608603955487237361261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43115478138607316316481681 32336608603955487237361261)
          ·
            refine ⟨12126228226483307714010473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32336608603955487237361261 12126228226483307714010473)
            ·
              refine ⟨9094671169862480785507855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12126228226483307714010473 9094671169862480785507855)
              ·
                refine ⟨13642006754793721178261783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9094671169862480785507855 13642006754793721178261783)
                ·
                  refine ⟨20463010132190581767392675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13642006754793721178261783 20463010132190581767392675)
                  ·
                    refine ⟨30694515198285872651089013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20463010132190581767392675 30694515198285872651089013)
                    ·
                      refine ⟨2877610799839300561039595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30694515198285872651089013 2877610799839300561039595)
                      ·
                        rfl

theorem cell23_5604127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_5604127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604127 prefixEnd_5604127 := by exact prefixLift 5604127
  have htrace : WordTrace (prefixWord ++ tailWord_5604127) baseStart_5604127 baseEnd_5604127 := by
    simpa [prefixWord, tailWord_5604127, baseEnd_5604127] using wordTrace_append hprefix tailTrace_5604127
  have hstable : (prefixWord ++ tailWord_5604127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604127).length < 2 ^ (prefixWord ++ tailWord_5604127).sum := by decide
  have hdescent : baseEnd_5604127 < baseStart_5604127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604130 : List Nat := [3, 3, 1, 1, 2, 2, 11]
def baseStart_5604130 : Nat := 118140960795 + 5604130 * 2 ^ 59
def prefixEnd_5604130 : Nat := 4983230072969 + 3 ^ 40 * 5604130 * 2
def baseEnd_5604130 : Nat := 35526078275077333942001

theorem tailTrace_5604130 : CollatzResearch.WordTrace tailWord_5604130 prefixEnd_5604130 35526078275077333942001 := by
  unfold tailWord_5604130
  simp only [CollatzResearch.WordTrace]
  refine ⟨51099853296800398512438461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136266275458134396033169229 51099853296800398512438461)
  ·
    refine ⟨19162444986300149442164423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51099853296800398512438461 19162444986300149442164423)
    ·
      refine ⟨28743667479450224163246635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19162444986300149442164423 28743667479450224163246635)
      ·
        refine ⟨43115501219175336244869953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28743667479450224163246635 43115501219175336244869953)
        ·
          refine ⟨32336625914381502183652465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43115501219175336244869953 32336625914381502183652465)
          ·
            refine ⟨24252469435786126637739349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32336625914381502183652465 24252469435786126637739349)
            ·
              refine ⟨35526078275077333942001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 24252469435786126637739349 35526078275077333942001)
              ·
                rfl

theorem cell23_5604130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 11].length) (baseStart_5604130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604130 prefixEnd_5604130 := by exact prefixLift 5604130
  have htrace : WordTrace (prefixWord ++ tailWord_5604130) baseStart_5604130 baseEnd_5604130 := by
    simpa [prefixWord, tailWord_5604130, baseEnd_5604130] using wordTrace_append hprefix tailTrace_5604130
  have hstable : (prefixWord ++ tailWord_5604130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604130).length < 2 ^ (prefixWord ++ tailWord_5604130).sum := by decide
  have hdescent : baseEnd_5604130 < baseStart_5604130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604158 : List Nat := [4, 2, 1, 2, 4, 1, 1, 2, 1, 1, 4]
def baseStart_5604158 : Nat := 118140960795 + 5604158 * 2 ^ 59
def prefixEnd_5604158 : Nat := 4983230072969 + 3 ^ 40 * 5604158 * 2
def baseEnd_5604158 : Nat := 2877626717739589939751953

theorem tailTrace_5604158 : CollatzResearch.WordTrace tailWord_5604158 prefixEnd_5604158 2877626717739589939751953 := by
  unfold tailWord_5604158
  simp only [CollatzResearch.WordTrace]
  refine ⟨25550054303887519353971641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136266956287400103221182085 25550054303887519353971641)
  ·
    refine ⟨19162540727915639515478731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25550054303887519353971641 19162540727915639515478731)
    ·
      refine ⟨28743811091873459273218097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19162540727915639515478731 28743811091873459273218097)
      ·
        refine ⟨21557858318905094454913573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28743811091873459273218097 21557858318905094454913573)
        ·
          refine ⟨4042098434794705210296295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21557858318905094454913573 4042098434794705210296295)
          ·
            refine ⟨6063147652192057815444443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4042098434794705210296295 6063147652192057815444443)
            ·
              refine ⟨9094721478288086723166665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6063147652192057815444443 9094721478288086723166665)
              ·
                refine ⟨6821041108716065042374999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9094721478288086723166665 6821041108716065042374999)
                ·
                  refine ⟨10231561663074097563562499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6821041108716065042374999 10231561663074097563562499)
                  ·
                    refine ⟨15347342494611146345343749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10231561663074097563562499 15347342494611146345343749)
                    ·
                      refine ⟨2877626717739589939751953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15347342494611146345343749 2877626717739589939751953)
                      ·
                        rfl

theorem cell23_5604158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_5604158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604158 prefixEnd_5604158 := by exact prefixLift 5604158
  have htrace : WordTrace (prefixWord ++ tailWord_5604158) baseStart_5604158 baseEnd_5604158 := by
    simpa [prefixWord, tailWord_5604158, baseEnd_5604158] using wordTrace_append hprefix tailTrace_5604158
  have hstable : (prefixWord ++ tailWord_5604158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604158).length < 2 ^ (prefixWord ++ tailWord_5604158).sum := by decide
  have hdescent : baseEnd_5604158 < baseStart_5604158 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604161 : List Nat := [1, 2, 5, 3, 1, 1, 1, 1, 3, 2, 3]
def baseStart_5604161 : Nat := 118140960795 + 5604161 * 2 ^ 59
def prefixEnd_5604161 : Nat := 4983230072969 + 3 ^ 40 * 5604161 * 2
def baseEnd_5604161 : Nat := 2877628258181553428014439

theorem tailTrace_5604161 : CollatzResearch.WordTrace tailWord_5604161 prefixEnd_5604161 2877628258181553428014439 := by
  unfold tailWord_5604161
  simp only [CollatzResearch.WordTrace]
  refine ⟨204400543850089286344132337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136267029233392857562754891 204400543850089286344132337)
  ·
    refine ⟨153300407887566964758099253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204400543850089286344132337 153300407887566964758099253)
    ·
      refine ⟨14371913239459402946071805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153300407887566964758099253 14371913239459402946071805)
      ·
        refine ⟨5389467464797276104776927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14371913239459402946071805 5389467464797276104776927)
        ·
          refine ⟨8084201197195914157165391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5389467464797276104776927 8084201197195914157165391)
          ·
            refine ⟨12126301795793871235748087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8084201197195914157165391 12126301795793871235748087)
            ·
              refine ⟨18189452693690806853622131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12126301795793871235748087 18189452693690806853622131)
              ·
                refine ⟨27284179040536210280433197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18189452693690806853622131 27284179040536210280433197)
                ·
                  refine ⟨10231567140201078855162449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27284179040536210280433197 10231567140201078855162449)
                  ·
                    refine ⟨7673675355150809141371837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10231567140201078855162449 7673675355150809141371837)
                    ·
                      refine ⟨2877628258181553428014439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7673675355150809141371837 2877628258181553428014439)
                      ·
                        rfl

theorem cell23_5604161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_5604161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604161 prefixEnd_5604161 := by exact prefixLift 5604161
  have htrace : WordTrace (prefixWord ++ tailWord_5604161) baseStart_5604161 baseEnd_5604161 := by
    simpa [prefixWord, tailWord_5604161, baseEnd_5604161] using wordTrace_append hprefix tailTrace_5604161
  have hstable : (prefixWord ++ tailWord_5604161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604161).length < 2 ^ (prefixWord ++ tailWord_5604161).sum := by decide
  have hdescent : baseEnd_5604161 < baseStart_5604161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604170 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 2, 2, 5]
def baseStart_5604170 : Nat := 118140960795 + 5604170 * 2 ^ 59
def prefixEnd_5604170 : Nat := 4983230072969 + 3 ^ 40 * 5604170 * 2
def baseEnd_5604170 : Nat := 2877632879507443892801897

theorem tailTrace_5604170 : CollatzResearch.WordTrace tailWord_5604170 prefixEnd_5604170 2877632879507443892801897 := by
  unfold tailWord_5604170
  simp only [CollatzResearch.WordTrace]
  refine ⟨51100218026764170220302491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136267248071371120587473309 51100218026764170220302491)
  ·
    refine ⟨76650327040146255330453737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51100218026764170220302491 76650327040146255330453737)
    ·
      refine ⟨57487745280109691497840303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76650327040146255330453737 57487745280109691497840303)
      ·
        refine ⟨86231617920164537246760455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57487745280109691497840303 86231617920164537246760455)
        ·
          refine ⟨129347426880246805870140683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86231617920164537246760455 129347426880246805870140683)
          ·
            refine ⟨194021140320370208805211025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129347426880246805870140683 194021140320370208805211025)
            ·
              refine ⟨145515855240277656603908269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194021140320370208805211025 145515855240277656603908269)
              ·
                refine ⟨54568445715104121226465601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145515855240277656603908269 54568445715104121226465601)
                ·
                  refine ⟨40926334286328090919849201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54568445715104121226465601 40926334286328090919849201)
                  ·
                    refine ⟨30694750714746068189886901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40926334286328090919849201 30694750714746068189886901)
                    ·
                      refine ⟨2877632879507443892801897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30694750714746068189886901 2877632879507443892801897)
                      ·
                        rfl

theorem cell23_5604170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_5604170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604170 prefixEnd_5604170 := by exact prefixLift 5604170
  have htrace : WordTrace (prefixWord ++ tailWord_5604170) baseStart_5604170 baseEnd_5604170 := by
    simpa [prefixWord, tailWord_5604170, baseEnd_5604170] using wordTrace_append hprefix tailTrace_5604170
  have hstable : (prefixWord ++ tailWord_5604170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604170).length < 2 ^ (prefixWord ++ tailWord_5604170).sum := by decide
  have hdescent : baseEnd_5604170 < baseStart_5604170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604184 : List Nat := [2, 1, 2, 2, 1, 1, 1, 7, 1, 3, 2]
def baseStart_5604184 : Nat := 118140960795 + 5604184 * 2 ^ 59
def prefixEnd_5604184 : Nat := 4983230072969 + 3 ^ 40 * 5604184 * 2
def baseEnd_5604184 : Nat := 2877640068236606838026833

theorem tailTrace_5604184 : CollatzResearch.WordTrace tailWord_5604184 prefixEnd_5604184 2877640068236606838026833 := by
  unfold tailWord_5604184
  simp only [CollatzResearch.WordTrace]
  refine ⟨102200691364502980636109803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136267588486003974181479737 102200691364502980636109803)
  ·
    refine ⟨153301037046754470954164705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102200691364502980636109803 153301037046754470954164705)
    ·
      refine ⟨114975777785065853215623529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153301037046754470954164705 114975777785065853215623529)
      ·
        refine ⟨86231833338799389911717647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114975777785065853215623529 86231833338799389911717647)
        ·
          refine ⟨129347750008199084867576471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86231833338799389911717647 129347750008199084867576471)
          ·
            refine ⟨194021625012298627301364707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129347750008199084867576471 194021625012298627301364707)
            ·
              refine ⟨291032437518447940952047061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194021625012298627301364707 291032437518447940952047061)
              ·
                refine ⟨6821072754338623616063603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 291032437518447940952047061 6821072754338623616063603)
                ·
                  refine ⟨10231609131507935424095405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6821072754338623616063603 10231609131507935424095405)
                  ·
                    refine ⟨3836853424315475784035777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10231609131507935424095405 3836853424315475784035777)
                    ·
                      refine ⟨2877640068236606838026833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3836853424315475784035777 2877640068236606838026833)
                      ·
                        rfl

theorem cell23_5604184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 1, 3, 2].length) (baseStart_5604184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604184 prefixEnd_5604184 := by exact prefixLift 5604184
  have htrace : WordTrace (prefixWord ++ tailWord_5604184) baseStart_5604184 baseEnd_5604184 := by
    simpa [prefixWord, tailWord_5604184, baseEnd_5604184] using wordTrace_append hprefix tailTrace_5604184
  have hstable : (prefixWord ++ tailWord_5604184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604184).length < 2 ^ (prefixWord ++ tailWord_5604184).sum := by decide
  have hdescent : baseEnd_5604184 < baseStart_5604184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604247 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 4, 3, 3]
def baseStart_5604247 : Nat := 118140960795 + 5604247 * 2 ^ 59
def prefixEnd_5604247 : Nat := 4983230072969 + 3 ^ 40 * 5604247 * 2
def baseEnd_5604247 : Nat := 2877672417517840091539043

theorem tailTrace_5604247 : CollatzResearch.WordTrace tailWord_5604247 prefixEnd_5604247 2877672417517840091539043 := by
  unfold tailWord_5604247
  simp only [CollatzResearch.WordTrace]
  refine ⟨204403680527777723031762995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136269120351851815354508663 204403680527777723031762995)
  ·
    refine ⟨306605520791666584547644493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204403680527777723031762995 306605520791666584547644493)
    ·
      refine ⟨114977070296874969205366685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306605520791666584547644493 114977070296874969205366685)
      ·
        refine ⟨43116401361328113452012507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114977070296874969205366685 43116401361328113452012507)
        ·
          refine ⟨64674602041992170178018761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43116401361328113452012507 64674602041992170178018761)
          ·
            refine ⟨48505951531494127633514071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64674602041992170178018761 48505951531494127633514071)
            ·
              refine ⟨72758927297241191450271107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48505951531494127633514071 72758927297241191450271107)
              ·
                refine ⟨109138390945861787175406661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72758927297241191450271107 109138390945861787175406661)
                ·
                  refine ⟨20463448302349085095388749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109138390945861787175406661 20463448302349085095388749)
                  ·
                    refine ⟨7673793113380906910770781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20463448302349085095388749 7673793113380906910770781)
                    ·
                      refine ⟨2877672417517840091539043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7673793113380906910770781 2877672417517840091539043)
                      ·
                        rfl

theorem cell23_5604247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_5604247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604247 prefixEnd_5604247 := by exact prefixLift 5604247
  have htrace : WordTrace (prefixWord ++ tailWord_5604247) baseStart_5604247 baseEnd_5604247 := by
    simpa [prefixWord, tailWord_5604247, baseEnd_5604247] using wordTrace_append hprefix tailTrace_5604247
  have hstable : (prefixWord ++ tailWord_5604247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604247).length < 2 ^ (prefixWord ++ tailWord_5604247).sum := by decide
  have hdescent : baseEnd_5604247 < baseStart_5604247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604338 : List Nat := [3, 2, 1, 5, 1, 1, 2, 1, 2, 1, 4]
def baseStart_5604338 : Nat := 118140960795 + 5604338 * 2 ^ 59
def prefixEnd_5604338 : Nat := 4983230072969 + 3 ^ 40 * 5604338 * 2
def baseEnd_5604338 : Nat := 2877719144257399235501125

theorem tailTrace_5604338 : CollatzResearch.WordTrace tailWord_5604338 prefixEnd_5604338 2877719144257399235501125 := by
  unfold tailWord_5604338
  simp only [CollatzResearch.WordTrace]
  refine ⟨51101749892612011393331417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136271333046965363715550445 51101749892612011393331417)
  ·
    refine ⟨38326312419459008544998563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51101749892612011393331417 38326312419459008544998563)
    ·
      refine ⟨57489468629188512817497845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38326312419459008544998563 57489468629188512817497845)
      ·
        refine ⟨5389637683986423076640423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57489468629188512817497845 5389637683986423076640423)
        ·
          refine ⟨8084456525979634614960635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5389637683986423076640423 8084456525979634614960635)
          ·
            refine ⟨12126684788969451922440953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8084456525979634614960635 12126684788969451922440953)
            ·
              refine ⟨9095013591727088941830715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12126684788969451922440953 9095013591727088941830715)
              ·
                refine ⟨13642520387590633412746073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9095013591727088941830715 13642520387590633412746073)
                ·
                  refine ⟨10231890290692975059559555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13642520387590633412746073 10231890290692975059559555)
                  ·
                    refine ⟨15347835436039462589339333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10231890290692975059559555 15347835436039462589339333)
                    ·
                      refine ⟨2877719144257399235501125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15347835436039462589339333 2877719144257399235501125)
                      ·
                        rfl

theorem cell23_5604338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_5604338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604338 prefixEnd_5604338 := by exact prefixLift 5604338
  have htrace : WordTrace (prefixWord ++ tailWord_5604338) baseStart_5604338 baseEnd_5604338 := by
    simpa [prefixWord, tailWord_5604338, baseEnd_5604338] using wordTrace_append hprefix tailTrace_5604338
  have hstable : (prefixWord ++ tailWord_5604338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604338).length < 2 ^ (prefixWord ++ tailWord_5604338).sum := by decide
  have hdescent : baseEnd_5604338 < baseStart_5604338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604388 : List Nat := [2, 3, 1, 4, 1, 2, 1, 2, 3, 1, 3]
def baseStart_5604388 : Nat := 118140960795 + 5604388 * 2 ^ 59
def prefixEnd_5604388 : Nat := 4983230072969 + 3 ^ 40 * 5604388 * 2
def baseEnd_5604388 : Nat := 2877744818290124039875895

theorem tailTrace_5604388 : CollatzResearch.WordTrace tailWord_5604388 prefixEnd_5604388 2877744818290124039875895 := by
  unfold tailWord_5604388
  simp only [CollatzResearch.WordTrace]
  refine ⟨102204411610133452056322909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136272548813511269408430545 102204411610133452056322909)
  ·
    refine ⟨38326654353800044521121091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102204411610133452056322909 38326654353800044521121091)
    ·
      refine ⟨57489981530700066781681637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38326654353800044521121091 57489981530700066781681637)
      ·
        refine ⟨10779371537006262521565307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57489981530700066781681637 10779371537006262521565307)
        ·
          refine ⟨16169057305509393782347961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10779371537006262521565307 16169057305509393782347961)
          ·
            refine ⟨12126792979132045336760971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16169057305509393782347961 12126792979132045336760971)
            ·
              refine ⟨18190189468698068005141457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12126792979132045336760971 18190189468698068005141457)
              ·
                refine ⟨13642642101523551003856093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18190189468698068005141457 13642642101523551003856093)
                ·
                  refine ⟨5115990788071331626446035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13642642101523551003856093 5115990788071331626446035)
                  ·
                    refine ⟨7673986182106997439669053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5115990788071331626446035 7673986182106997439669053)
                    ·
                      refine ⟨2877744818290124039875895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7673986182106997439669053 2877744818290124039875895)
                      ·
                        rfl

theorem cell23_5604388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_5604388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604388 prefixEnd_5604388 := by exact prefixLift 5604388
  have htrace : WordTrace (prefixWord ++ tailWord_5604388) baseStart_5604388 baseEnd_5604388 := by
    simpa [prefixWord, tailWord_5604388, baseEnd_5604388] using wordTrace_append hprefix tailTrace_5604388
  have hstable : (prefixWord ++ tailWord_5604388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604388).length < 2 ^ (prefixWord ++ tailWord_5604388).sum := by decide
  have hdescent : baseEnd_5604388 < baseStart_5604388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604391 : List Nat := [1, 1, 7, 1, 1, 1, 2, 1, 3, 5]
def baseStart_5604391 : Nat := 118140960795 + 5604391 * 2 ^ 59
def prefixEnd_5604391 : Nat := 4983230072969 + 3 ^ 40 * 5604391 * 2
def baseEnd_5604391 : Nat := 959248786244029176046127

theorem tailTrace_5604391 : CollatzResearch.WordTrace tailWord_5604391 prefixEnd_5604391 959248786244029176046127 := by
  unfold tailWord_5604391
  simp only [CollatzResearch.WordTrace]
  refine ⟨204408932639256035625005027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136272621759504023750003351 204408932639256035625005027)
  ·
    refine ⟨306613398958884053437507541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204408932639256035625005027 306613398958884053437507541)
    ·
      refine ⟨7186251538098845002441583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 306613398958884053437507541 7186251538098845002441583)
      ·
        refine ⟨10779377307148267503662375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7186251538098845002441583 10779377307148267503662375)
        ·
          refine ⟨16169065960722401255493563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10779377307148267503662375 16169065960722401255493563)
          ·
            refine ⟨24253598941083601883240345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16169065960722401255493563 24253598941083601883240345)
            ·
              refine ⟨18190199205812701412430259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24253598941083601883240345 18190199205812701412430259)
              ·
                refine ⟨27285298808719052118645389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18190199205812701412430259 27285298808719052118645389)
                ·
                  refine ⟨10231987053269644544492021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27285298808719052118645389 10231987053269644544492021)
                  ·
                    refine ⟨959248786244029176046127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10231987053269644544492021 959248786244029176046127)
                    ·
                      rfl

theorem cell23_5604391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_5604391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604391 prefixEnd_5604391 := by exact prefixLift 5604391
  have htrace : WordTrace (prefixWord ++ tailWord_5604391) baseStart_5604391 baseEnd_5604391 := by
    simpa [prefixWord, tailWord_5604391, baseEnd_5604391] using wordTrace_append hprefix tailTrace_5604391
  have hstable : (prefixWord ++ tailWord_5604391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604391).length < 2 ^ (prefixWord ++ tailWord_5604391).sum := by decide
  have hdescent : baseEnd_5604391 < baseStart_5604391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604407 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 6]
def baseStart_5604407 : Nat := 118140960795 + 5604407 * 2 ^ 59
def prefixEnd_5604407 : Nat := 4983230072969 + 3 ^ 40 * 5604407 * 2
def baseEnd_5604407 : Nat := 2877754574422559465538307

theorem tailTrace_5604407 : CollatzResearch.WordTrace tailWord_5604407 prefixEnd_5604407 2877754574422559465538307 := by
  unfold tailWord_5604407
  simp only [CollatzResearch.WordTrace]
  refine ⟨204409516207198070357587475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136273010804798713571724983 204409516207198070357587475)
  ·
    refine ⟨306614274310797105536381213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204409516207198070357587475 306614274310797105536381213)
    ·
      refine ⟨114980352866548914576142955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306614274310797105536381213 114980352866548914576142955)
      ·
        refine ⟨172470529299823371864214433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114980352866548914576142955 172470529299823371864214433)
        ·
          refine ⟨129352896974867528898160825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172470529299823371864214433 129352896974867528898160825)
          ·
            refine ⟨97014672731150646673620619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129352896974867528898160825 97014672731150646673620619)
            ·
              refine ⟨145522009096725970010430929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97014672731150646673620619 145522009096725970010430929)
              ·
                refine ⟨109141506822544477507823197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145522009096725970010430929 109141506822544477507823197)
                ·
                  refine ⟨40928065058454179065433699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109141506822544477507823197 40928065058454179065433699)
                  ·
                    refine ⟨61392097587681268598150549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40928065058454179065433699 61392097587681268598150549)
                    ·
                      refine ⟨2877754574422559465538307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61392097587681268598150549 2877754574422559465538307)
                      ·
                        rfl

theorem cell23_5604407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_5604407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604407 prefixEnd_5604407 := by exact prefixLift 5604407
  have htrace : WordTrace (prefixWord ++ tailWord_5604407) baseStart_5604407 baseEnd_5604407 := by
    simpa [prefixWord, tailWord_5604407, baseEnd_5604407] using wordTrace_append hprefix tailTrace_5604407
  have hstable : (prefixWord ++ tailWord_5604407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604407).length < 2 ^ (prefixWord ++ tailWord_5604407).sum := by decide
  have hdescent : baseEnd_5604407 < baseStart_5604407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604408 : List Nat := [2, 1, 2, 1, 5, 3, 2, 1, 1, 5]
def baseStart_5604408 : Nat := 118140960795 + 5604408 * 2 ^ 59
def prefixEnd_5604408 : Nat := 4983230072969 + 3 ^ 40 * 5604408 * 2
def baseEnd_5604408 : Nat := 959251695967737987208601

theorem tailTrace_5604408 : CollatzResearch.WordTrace tailWord_5604408 prefixEnd_5604408 959251695967737987208601 := by
  unfold tailWord_5604408
  simp only [CollatzResearch.WordTrace]
  refine ⟨102204776340097223764186939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136273035120129631685582585 102204776340097223764186939)
  ·
    refine ⟨153307164510145835646280409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102204776340097223764186939 153307164510145835646280409)
    ·
      refine ⟨114980373382609376734710307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153307164510145835646280409 114980373382609376734710307)
      ·
        refine ⟨172470560073914065102065461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114980373382609376734710307 172470560073914065102065461)
        ·
          refine ⟨16169115006929443603318637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 172470560073914065102065461 16169115006929443603318637)
          ·
            refine ⟨6063418127598541351244489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16169115006929443603318637 6063418127598541351244489)
            ·
              refine ⟨4547563595698906013433367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6063418127598541351244489 4547563595698906013433367)
              ·
                refine ⟨6821345393548359020150051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4547563595698906013433367 6821345393548359020150051)
                ·
                  refine ⟨10232018090322538530225077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6821345393548359020150051 10232018090322538530225077)
                  ·
                    refine ⟨959251695967737987208601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10232018090322538530225077 959251695967737987208601)
                    ·
                      rfl

theorem cell23_5604408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 1, 5].length) (baseStart_5604408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604408 prefixEnd_5604408 := by exact prefixLift 5604408
  have htrace : WordTrace (prefixWord ++ tailWord_5604408) baseStart_5604408 baseEnd_5604408 := by
    simpa [prefixWord, tailWord_5604408, baseEnd_5604408] using wordTrace_append hprefix tailTrace_5604408
  have hstable : (prefixWord ++ tailWord_5604408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604408).length < 2 ^ (prefixWord ++ tailWord_5604408).sum := by decide
  have hdescent : baseEnd_5604408 < baseStart_5604408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604421 : List Nat := [1, 3, 1, 1, 1, 3, 5, 2, 2, 4]
def baseStart_5604421 : Nat := 118140960795 + 5604421 * 2 ^ 59
def prefixEnd_5604421 : Nat := 4983230072969 + 3 ^ 40 * 5604421 * 2
def baseEnd_5604421 : Nat := 959253921050574136921081

theorem tailTrace_5604421 : CollatzResearch.WordTrace tailWord_5604421 prefixEnd_5604421 959253921050574136921081 := by
  unfold tailWord_5604421
  simp only [CollatzResearch.WordTrace]
  refine ⟨204410026829147350748597117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136273351219431567165731411 204410026829147350748597117)
  ·
    refine ⟨76653760060930256530723919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204410026829147350748597117 76653760060930256530723919)
    ·
      refine ⟨114980640091395384796085879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76653760060930256530723919 114980640091395384796085879)
      ·
        refine ⟨172470960137093077194128819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114980640091395384796085879 172470960137093077194128819)
        ·
          refine ⟨258706440205639615791193229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172470960137093077194128819 258706440205639615791193229)
          ·
            refine ⟨97014915077114855921697461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 258706440205639615791193229 97014915077114855921697461)
            ·
              refine ⟨9095148288479517742659137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97014915077114855921697461 9095148288479517742659137)
              ·
                refine ⟨6821361216359638306994353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9095148288479517742659137 6821361216359638306994353)
                ·
                  refine ⟨5116020912269728730245765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6821361216359638306994353 5116020912269728730245765)
                  ·
                    refine ⟨959253921050574136921081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5116020912269728730245765 959253921050574136921081)
                    ·
                      rfl

theorem cell23_5604421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 2, 4].length) (baseStart_5604421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604421 prefixEnd_5604421 := by exact prefixLift 5604421
  have htrace : WordTrace (prefixWord ++ tailWord_5604421) baseStart_5604421 baseEnd_5604421 := by
    simpa [prefixWord, tailWord_5604421, baseEnd_5604421] using wordTrace_append hprefix tailTrace_5604421
  have hstable : (prefixWord ++ tailWord_5604421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604421).length < 2 ^ (prefixWord ++ tailWord_5604421).sum := by decide
  have hdescent : baseEnd_5604421 < baseStart_5604421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604422 : List Nat := [6, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3]
def baseStart_5604422 : Nat := 118140960795 + 5604422 * 2 ^ 59
def prefixEnd_5604422 : Nat := 4983230072969 + 3 ^ 40 * 5604422 * 2
def baseEnd_5604422 : Nat := 2877762276632376906850739

theorem tailTrace_5604422 : CollatzResearch.WordTrace tailWord_5604422 prefixEnd_5604422 2877762276632376906850739 := by
  unfold tailWord_5604422
  simp only [CollatzResearch.WordTrace]
  refine ⟨6387814478191991497480735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 136273375534762485279589013 6387814478191991497480735)
  ·
    refine ⟨9581721717287987246221103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6387814478191991497480735 9581721717287987246221103)
    ·
      refine ⟨14372582575931980869331655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9581721717287987246221103 14372582575931980869331655)
      ·
        refine ⟨21558873863897971303997483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14372582575931980869331655 21558873863897971303997483)
        ·
          refine ⟨32338310795846956955996225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21558873863897971303997483 32338310795846956955996225)
          ·
            refine ⟨24253733096885217716997169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32338310795846956955996225 24253733096885217716997169)
            ·
              refine ⟨18190299822663913287747877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24253733096885217716997169 18190299822663913287747877)
              ·
                refine ⟨3410681216749483741452727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18190299822663913287747877 3410681216749483741452727)
                ·
                  refine ⟨5116021825124225612179091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3410681216749483741452727 5116021825124225612179091)
                  ·
                    refine ⟨7674032737686338418268637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5116021825124225612179091 7674032737686338418268637)
                    ·
                      refine ⟨2877762276632376906850739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7674032737686338418268637 2877762276632376906850739)
                      ·
                        rfl

theorem cell23_5604422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_5604422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604422 prefixEnd_5604422 := by exact prefixLift 5604422
  have htrace : WordTrace (prefixWord ++ tailWord_5604422) baseStart_5604422 baseEnd_5604422 := by
    simpa [prefixWord, tailWord_5604422, baseEnd_5604422] using wordTrace_append hprefix tailTrace_5604422
  have hstable : (prefixWord ++ tailWord_5604422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604422).length < 2 ^ (prefixWord ++ tailWord_5604422).sum := by decide
  have hdescent : baseEnd_5604422 < baseStart_5604422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604445 : List Nat := [1, 4, 4, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_5604445 : Nat := 118140960795 + 5604445 * 2 ^ 59
def prefixEnd_5604445 : Nat := 4983230072969 + 3 ^ 40 * 5604445 * 2
def baseEnd_5604445 : Nat := 2877774086687430316863133

theorem tailTrace_5604445 : CollatzResearch.WordTrace tailWord_5604445 prefixEnd_5604445 2877774086687430316863133 := by
  unfold tailWord_5604445
  simp only [CollatzResearch.WordTrace]
  refine ⟨204410902181060402847470789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136273934787373601898313859 204410902181060402847470789)
  ·
    refine ⟨38327044158948825533900773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204410902181060402847470789 38327044158948825533900773)
    ·
      refine ⟨7186320779802904787606395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38327044158948825533900773 7186320779802904787606395)
      ·
        refine ⟨10779481169704357181409593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7186320779802904787606395 10779481169704357181409593)
        ·
          refine ⟨8084610877278267886057195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10779481169704357181409593 8084610877278267886057195)
          ·
            refine ⟨12126916315917401829085793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8084610877278267886057195 12126916315917401829085793)
            ·
              refine ⟨9095187236938051371814345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12126916315917401829085793 9095187236938051371814345)
              ·
                refine ⟨6821390427703538528860759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9095187236938051371814345 6821390427703538528860759)
                ·
                  refine ⟨10232085641555307793291139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6821390427703538528860759 10232085641555307793291139)
                  ·
                    refine ⟨15348128462332961689936709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10232085641555307793291139 15348128462332961689936709)
                    ·
                      refine ⟨2877774086687430316863133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15348128462332961689936709 2877774086687430316863133)
                      ·
                        rfl

theorem cell23_5604445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_5604445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604445 prefixEnd_5604445 := by exact prefixLift 5604445
  have htrace : WordTrace (prefixWord ++ tailWord_5604445) baseStart_5604445 baseEnd_5604445 := by
    simpa [prefixWord, tailWord_5604445, baseEnd_5604445] using wordTrace_append hprefix tailTrace_5604445
  have hstable : (prefixWord ++ tailWord_5604445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604445).length < 2 ^ (prefixWord ++ tailWord_5604445).sum := by decide
  have hdescent : baseEnd_5604445 < baseStart_5604445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604462 : List Nat := [4, 1, 2, 2, 1, 2, 3, 3, 1, 2, 2]
def baseStart_5604462 : Nat := 118140960795 + 5604462 * 2 ^ 59
def prefixEnd_5604462 : Nat := 4983230072969 + 3 ^ 40 * 5604462 * 2
def baseEnd_5604462 : Nat := 2877782815858556750350555

theorem tailTrace_5604462 : CollatzResearch.WordTrace tailWord_5604462 prefixEnd_5604462 2877782815858556750350555 := by
  unfold tailWord_5604462
  simp only [CollatzResearch.WordTrace]
  refine ⟨25551440277749851843854955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136274348147999209833893093 25551440277749851843854955)
  ·
    refine ⟨38327160416624777765782433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25551440277749851843854955 38327160416624777765782433)
    ·
      refine ⟨28745370312468583324336825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38327160416624777765782433 28745370312468583324336825)
      ·
        refine ⟨21559027734351437493252619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28745370312468583324336825 21559027734351437493252619)
        ·
          refine ⟨32338541601527156239878929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21559027734351437493252619 32338541601527156239878929)
          ·
            refine ⟨24253906201145367179909197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32338541601527156239878929 24253906201145367179909197)
            ·
              refine ⟨9095214825429512692465949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24253906201145367179909197 9095214825429512692465949)
              ·
                refine ⟨3410705559536067259674731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9095214825429512692465949 3410705559536067259674731)
                ·
                  refine ⟨5116058339304100889512097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3410705559536067259674731 5116058339304100889512097)
                  ·
                    refine ⟨3837043754478075667134073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5116058339304100889512097 3837043754478075667134073)
                    ·
                      refine ⟨2877782815858556750350555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3837043754478075667134073 2877782815858556750350555)
                      ·
                        rfl

theorem cell23_5604462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_5604462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604462 prefixEnd_5604462 := by exact prefixLift 5604462
  have htrace : WordTrace (prefixWord ++ tailWord_5604462) baseStart_5604462 baseEnd_5604462 := by
    simpa [prefixWord, tailWord_5604462, baseEnd_5604462] using wordTrace_append hprefix tailTrace_5604462
  have hstable : (prefixWord ++ tailWord_5604462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604462).length < 2 ^ (prefixWord ++ tailWord_5604462).sum := by decide
  have hdescent : baseEnd_5604462 < baseStart_5604462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604467 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 8]
def baseStart_5604467 : Nat := 118140960795 + 5604467 * 2 ^ 59
def prefixEnd_5604467 : Nat := 4983230072969 + 3 ^ 40 * 5604467 * 2
def baseEnd_5604467 : Nat := 2877785383261829230788031

theorem tailTrace_5604467 : CollatzResearch.WordTrace tailWord_5604467 prefixEnd_5604467 2877785383261829230788031 := by
  unfold tailWord_5604467
  simp only [CollatzResearch.WordTrace]
  refine ⟨204411704586980700604771655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136274469724653800403181103 204411704586980700604771655)
  ·
    refine ⟨306617556880471050907157483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204411704586980700604771655 306617556880471050907157483)
    ·
      refine ⟨459926335320706576360736225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306617556880471050907157483 459926335320706576360736225)
      ·
        refine ⟨344944751490529932270552169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 459926335320706576360736225 344944751490529932270552169)
        ·
          refine ⟨258708563617897449202914127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344944751490529932270552169 258708563617897449202914127)
          ·
            refine ⟨388062845426846173804371191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258708563617897449202914127 388062845426846173804371191)
            ·
              refine ⟨582094268140269260706556787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388062845426846173804371191 582094268140269260706556787)
              ·
                refine ⟨873141402210403891059835181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 582094268140269260706556787 873141402210403891059835181)
                ·
                  refine ⟨327428025828901459147438193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 873141402210403891059835181 327428025828901459147438193)
                  ·
                    refine ⟨245571019371676094360578645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 327428025828901459147438193 245571019371676094360578645)
                    ·
                      refine ⟨2877785383261829230788031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 245571019371676094360578645 2877785383261829230788031)
                      ·
                        rfl

theorem cell23_5604467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 8].length) (baseStart_5604467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604467 prefixEnd_5604467 := by exact prefixLift 5604467
  have htrace : WordTrace (prefixWord ++ tailWord_5604467) baseStart_5604467 baseEnd_5604467 := by
    simpa [prefixWord, tailWord_5604467, baseEnd_5604467] using wordTrace_append hprefix tailTrace_5604467
  have hstable : (prefixWord ++ tailWord_5604467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604467).length < 2 ^ (prefixWord ++ tailWord_5604467).sum := by decide
  have hdescent : baseEnd_5604467 < baseStart_5604467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604535 : List Nat := [1, 1, 3, 1, 4, 1, 4, 2, 2, 2, 2]
def baseStart_5604535 : Nat := 118140960795 + 5604535 * 2 ^ 59
def prefixEnd_5604535 : Nat := 4983230072969 + 3 ^ 40 * 5604535 * 2
def baseEnd_5604535 : Nat := 2877820299946334964737719

theorem tailTrace_5604535 : CollatzResearch.WordTrace tailWord_5604535 prefixEnd_5604535 2877820299946334964737719 := by
  unfold tailWord_5604535
  simp only [CollatzResearch.WordTrace]
  refine ⟨204414184750734348218247059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136276123167156232145498039 204414184750734348218247059)
  ·
    refine ⟨306621277126101522327370589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204414184750734348218247059 306621277126101522327370589)
    ·
      refine ⟨114982978922288070872763971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306621277126101522327370589 114982978922288070872763971)
      ·
        refine ⟨172474468383432106309145957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114982978922288070872763971 172474468383432106309145957)
        ·
          refine ⟨32338962821893519932964867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172474468383432106309145957 32338962821893519932964867)
          ·
            refine ⟨48508444232840279899447301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32338962821893519932964867 48508444232840279899447301)
            ·
              refine ⟨9095333293657552481146369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48508444232840279899447301 9095333293657552481146369)
              ·
                refine ⟨6821499970243164360859777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9095333293657552481146369 6821499970243164360859777)
                ·
                  refine ⟨5116124977682373270644833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6821499970243164360859777 5116124977682373270644833)
                  ·
                    refine ⟨3837093733261779952983625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5116124977682373270644833 3837093733261779952983625)
                    ·
                      refine ⟨2877820299946334964737719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3837093733261779952983625 2877820299946334964737719)
                      ·
                        rfl

theorem cell23_5604535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 2, 2, 2].length) (baseStart_5604535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604535 prefixEnd_5604535 := by exact prefixLift 5604535
  have htrace : WordTrace (prefixWord ++ tailWord_5604535) baseStart_5604535 baseEnd_5604535 := by
    simpa [prefixWord, tailWord_5604535, baseEnd_5604535] using wordTrace_append hprefix tailTrace_5604535
  have hstable : (prefixWord ++ tailWord_5604535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604535).length < 2 ^ (prefixWord ++ tailWord_5604535).sum := by decide
  have hdescent : baseEnd_5604535 < baseStart_5604535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604548 : List Nat := [2, 3, 3, 1, 3, 1, 1, 1, 2, 2, 4]
def baseStart_5604548 : Nat := 118140960795 + 5604548 * 2 ^ 59
def prefixEnd_5604548 : Nat := 4983230072969 + 3 ^ 40 * 5604548 * 2
def baseEnd_5604548 : Nat := 2877826975194843413875159

theorem tailTrace_5604548 : CollatzResearch.WordTrace tailWord_5604548 prefixEnd_5604548 2877826975194843413875159 := by
  unfold tailWord_5604548
  simp only [CollatzResearch.WordTrace]
  refine ⟨102207329449843625719235149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136276439266458167625646865 102207329449843625719235149)
  ·
    refine ⟨38327748543691359644713181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102207329449843625719235149 38327748543691359644713181)
    ·
      refine ⟨14372905703884259866767443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38327748543691359644713181 14372905703884259866767443)
      ·
        refine ⟨21559358555826389800151165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14372905703884259866767443 21559358555826389800151165)
        ·
          refine ⟨8084759458434896175056687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21559358555826389800151165 8084759458434896175056687)
          ·
            refine ⟨12127139187652344262585031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8084759458434896175056687 12127139187652344262585031)
            ·
              refine ⟨18190708781478516393877547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12127139187652344262585031 18190708781478516393877547)
              ·
                refine ⟨27286063172217774590816321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18190708781478516393877547 27286063172217774590816321)
                ·
                  refine ⟨20464547379163330943112241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27286063172217774590816321 20464547379163330943112241)
                  ·
                    refine ⟨15348410534372498207334181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20464547379163330943112241 15348410534372498207334181)
                    ·
                      refine ⟨2877826975194843413875159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15348410534372498207334181 2877826975194843413875159)
                      ·
                        rfl

theorem cell23_5604548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_5604548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604548 prefixEnd_5604548 := by exact prefixLift 5604548
  have htrace : WordTrace (prefixWord ++ tailWord_5604548) baseStart_5604548 baseEnd_5604548 := by
    simpa [prefixWord, tailWord_5604548, baseEnd_5604548] using wordTrace_append hprefix tailTrace_5604548
  have hstable : (prefixWord ++ tailWord_5604548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604548).length < 2 ^ (prefixWord ++ tailWord_5604548).sum := by decide
  have hdescent : baseEnd_5604548 < baseStart_5604548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604561 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 4, 5, 2]
def baseStart_5604561 : Nat := 118140960795 + 5604561 * 2 ^ 59
def prefixEnd_5604561 : Nat := 4983230072969 + 3 ^ 40 * 5604561 * 2
def baseEnd_5604561 : Nat := 2877833650443351863012599

theorem tailTrace_5604561 : CollatzResearch.WordTrace tailWord_5604561 prefixEnd_5604561 2877833650443351863012599 := by
  unfold tailWord_5604561
  simp only [CollatzResearch.WordTrace]
  refine ⟨204415133048640154658693537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136276755365760103105795691 204415133048640154658693537)
  ·
    refine ⟨153311349786480115994020153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204415133048640154658693537 153311349786480115994020153)
    ·
      refine ⟨114983512339860086995515115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153311349786480115994020153 114983512339860086995515115)
      ·
        refine ⟨172475268509790130493272673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114983512339860086995515115 172475268509790130493272673)
        ·
          refine ⟨129356451382342597869954505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172475268509790130493272673 129356451382342597869954505)
          ·
            refine ⟨97017338536756948402465879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129356451382342597869954505 97017338536756948402465879)
            ·
              refine ⟨145526007805135422603698819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97017338536756948402465879 145526007805135422603698819)
              ·
                refine ⟨218289011707703133905548229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145526007805135422603698819 218289011707703133905548229)
                ·
                  refine ⟨40929189695194337607290293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 218289011707703133905548229 40929189695194337607290293)
                  ·
                    refine ⟨3837111533924469150683465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40929189695194337607290293 3837111533924469150683465)
                    ·
                      refine ⟨2877833650443351863012599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3837111533924469150683465 2877833650443351863012599)
                      ·
                        rfl

theorem cell23_5604561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 5, 2].length) (baseStart_5604561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604561 prefixEnd_5604561 := by exact prefixLift 5604561
  have htrace : WordTrace (prefixWord ++ tailWord_5604561) baseStart_5604561 baseEnd_5604561 := by
    simpa [prefixWord, tailWord_5604561, baseEnd_5604561] using wordTrace_append hprefix tailTrace_5604561
  have hstable : (prefixWord ++ tailWord_5604561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604561).length < 2 ^ (prefixWord ++ tailWord_5604561).sum := by decide
  have hdescent : baseEnd_5604561 < baseStart_5604561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604611 : List Nat := [1, 1, 1, 3, 2, 4, 1, 2, 1, 4, 3]
def baseStart_5604611 : Nat := 118140960795 + 5604611 * 2 ^ 59
def prefixEnd_5604611 : Nat := 4983230072969 + 3 ^ 40 * 5604611 * 2
def baseEnd_5604611 : Nat := 2877859324476076667387369

theorem tailTrace_5604611 : CollatzResearch.WordTrace tailWord_5604611 prefixEnd_5604611 2877859324476076667387369 := by
  unfold tailWord_5604611
  simp only [CollatzResearch.WordTrace]
  refine ⟨204416956698459013198013687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136277971132306008798675791 204416956698459013198013687)
  ·
    refine ⟨306625435047688519797020531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204416956698459013198013687 306625435047688519797020531)
    ·
      refine ⟨459938152571532779695530797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306625435047688519797020531 459938152571532779695530797)
      ·
        refine ⟨172476807214324792385824049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 459938152571532779695530797 172476807214324792385824049)
        ·
          refine ⟨129357605410743594289368037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172476807214324792385824049 129357605410743594289368037)
          ·
            refine ⟨24254551014514423929256507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129357605410743594289368037 24254551014514423929256507)
            ·
              refine ⟨36381826521771635893884761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24254551014514423929256507 36381826521771635893884761)
              ·
                refine ⟨27286369891328726920413571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36381826521771635893884761 27286369891328726920413571)
                ·
                  refine ⟨40929554836993090380620357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27286369891328726920413571 40929554836993090380620357)
                  ·
                    refine ⟨7674291531936204446366317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40929554836993090380620357 7674291531936204446366317)
                    ·
                      refine ⟨2877859324476076667387369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7674291531936204446366317 2877859324476076667387369)
                      ·
                        rfl

theorem cell23_5604611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 4, 3].length) (baseStart_5604611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604611 prefixEnd_5604611 := by exact prefixLift 5604611
  have htrace : WordTrace (prefixWord ++ tailWord_5604611) baseStart_5604611 baseEnd_5604611 := by
    simpa [prefixWord, tailWord_5604611, baseEnd_5604611] using wordTrace_append hprefix tailTrace_5604611
  have hstable : (prefixWord ++ tailWord_5604611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604611).length < 2 ^ (prefixWord ++ tailWord_5604611).sum := by decide
  have hdescent : baseEnd_5604611 < baseStart_5604611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604691 : List Nat := [1, 1, 1, 2, 1, 1, 7, 2, 1, 6]
def baseStart_5604691 : Nat := 118140960795 + 5604691 * 2 ^ 59
def prefixEnd_5604691 : Nat := 4983230072969 + 3 ^ 40 * 5604691 * 2
def baseEnd_5604691 : Nat := 959300134309478784795667

theorem tailTrace_5604691 : CollatzResearch.WordTrace tailWord_5604691 prefixEnd_5604691 959300134309478784795667 := by
  unfold tailWord_5604691
  simp only [CollatzResearch.WordTrace]
  refine ⟨204419874538169186860925927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136279916358779457907283951 204419874538169186860925927)
  ·
    refine ⟨306629811807253780291388891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204419874538169186860925927 306629811807253780291388891)
    ·
      refine ⟨459944717710880670437083337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306629811807253780291388891 459944717710880670437083337)
      ·
        refine ⟨344958538283160502827812503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 459944717710880670437083337 344958538283160502827812503)
        ·
          refine ⟨517437807424740754241718755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344958538283160502827812503 517437807424740754241718755)
          ·
            refine ⟨776156711137111131362578133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 517437807424740754241718755 776156711137111131362578133)
            ·
              refine ⟨18191172917276042141310425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 776156711137111131362578133 18191172917276042141310425)
              ·
                refine ⟨13643379687957031605982819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18191172917276042141310425 13643379687957031605982819)
                ·
                  refine ⟨20465069531935547408974229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13643379687957031605982819 20465069531935547408974229)
                  ·
                    refine ⟨959300134309478784795667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20465069531935547408974229 959300134309478784795667)
                    ·
                      rfl

theorem cell23_5604691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 6].length) (baseStart_5604691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604691 prefixEnd_5604691 := by exact prefixLift 5604691
  have htrace : WordTrace (prefixWord ++ tailWord_5604691) baseStart_5604691 baseEnd_5604691 := by
    simpa [prefixWord, tailWord_5604691, baseEnd_5604691] using wordTrace_append hprefix tailTrace_5604691
  have hstable : (prefixWord ++ tailWord_5604691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604691).length < 2 ^ (prefixWord ++ tailWord_5604691).sum := by decide
  have hdescent : baseEnd_5604691 < baseStart_5604691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604692 : List Nat := [2, 4, 1, 1, 2, 1, 2, 5, 1, 1, 3]
def baseStart_5604692 : Nat := 118140960795 + 5604692 * 2 ^ 59
def prefixEnd_5604692 : Nat := 4983230072969 + 3 ^ 40 * 5604692 * 2
def baseEnd_5604692 : Nat := 2877900916409090850474497

theorem tailTrace_5604692 : CollatzResearch.WordTrace tailWord_5604692 prefixEnd_5604692 2877900916409090850474497 := by
  unfold tailWord_5604692
  simp only [CollatzResearch.WordTrace]
  refine ⟨102209955505582782015856165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136279940674110376021141553 102209955505582782015856165)
  ·
    refine ⟨19164366657296771627973031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102209955505582782015856165 19164366657296771627973031)
    ·
      refine ⟨28746549985945157441959547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19164366657296771627973031 28746549985945157441959547)
      ·
        refine ⟨43119824978917736162939321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28746549985945157441959547 43119824978917736162939321)
        ·
          refine ⟨32339868734188302122204491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43119824978917736162939321 32339868734188302122204491)
          ·
            refine ⟨48509803101282453183306737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32339868734188302122204491 48509803101282453183306737)
            ·
              refine ⟨36382352325961839887480053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48509803101282453183306737 36382352325961839887480053)
              ·
                refine ⟨3410845530558922489451255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36382352325961839887480053 3410845530558922489451255)
                ·
                  refine ⟨5116268295838383734176883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3410845530558922489451255 5116268295838383734176883)
                  ·
                    refine ⟨7674402443757575601265325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5116268295838383734176883 7674402443757575601265325)
                    ·
                      refine ⟨2877900916409090850474497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7674402443757575601265325 2877900916409090850474497)
                      ·
                        rfl

theorem cell23_5604692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_5604692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604692 prefixEnd_5604692 := by exact prefixLift 5604692
  have htrace : WordTrace (prefixWord ++ tailWord_5604692) baseStart_5604692 baseEnd_5604692 := by
    simpa [prefixWord, tailWord_5604692, baseEnd_5604692] using wordTrace_append hprefix tailTrace_5604692
  have hstable : (prefixWord ++ tailWord_5604692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604692).length < 2 ^ (prefixWord ++ tailWord_5604692).sum := by decide
  have hdescent : baseEnd_5604692 < baseStart_5604692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604695 : List Nat := [1, 1, 3, 2, 3, 3, 3, 1, 1, 5]
def baseStart_5604695 : Nat := 118140960795 + 5604695 * 2 ^ 59
def prefixEnd_5604695 : Nat := 4983230072969 + 3 ^ 40 * 5604695 * 2
def baseEnd_5604695 : Nat := 959300818950351446245661

theorem tailTrace_5604695 : CollatzResearch.WordTrace tailWord_5604695 prefixEnd_5604695 959300818950351446245661 := by
  unfold tailWord_5604695
  simp only [CollatzResearch.WordTrace]
  refine ⟨204420020430154695544071539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136280013620103130362714359 204420020430154695544071539)
  ·
    refine ⟨306630030645232043316107309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204420020430154695544071539 306630030645232043316107309)
    ·
      refine ⟨114986261491962016243540241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306630030645232043316107309 114986261491962016243540241)
      ·
        refine ⟨86239696118971512182655181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114986261491962016243540241 86239696118971512182655181)
        ·
          refine ⟨32339886044614317068495693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86239696118971512182655181 32339886044614317068495693)
          ·
            refine ⟨12127457266730368900685885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32339886044614317068495693 12127457266730368900685885)
            ·
              refine ⟨4547796475023888337757207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12127457266730368900685885 4547796475023888337757207)
              ·
                refine ⟨6821694712535832506635811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4547796475023888337757207 6821694712535832506635811)
                ·
                  refine ⟨10232542068803748759953717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6821694712535832506635811 10232542068803748759953717)
                  ·
                    refine ⟨959300818950351446245661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10232542068803748759953717 959300818950351446245661)
                    ·
                      rfl

theorem cell23_5604695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 1, 5].length) (baseStart_5604695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604695 prefixEnd_5604695 := by exact prefixLift 5604695
  have htrace : WordTrace (prefixWord ++ tailWord_5604695) baseStart_5604695 baseEnd_5604695 := by
    simpa [prefixWord, tailWord_5604695, baseEnd_5604695] using wordTrace_append hprefix tailTrace_5604695
  have hstable : (prefixWord ++ tailWord_5604695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604695).length < 2 ^ (prefixWord ++ tailWord_5604695).sum := by decide
  have hdescent : baseEnd_5604695 < baseStart_5604695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604698 : List Nat := [3, 1, 1, 2, 1, 2, 2, 5, 1, 1, 4]
def baseStart_5604698 : Nat := 118140960795 + 5604698 * 2 ^ 59
def prefixEnd_5604698 : Nat := 4983230072969 + 3 ^ 40 * 5604698 * 2
def baseEnd_5604698 : Nat := 2877903997293017826999469

theorem tailTrace_5604698 : CollatzResearch.WordTrace tailWord_5604698 prefixEnd_5604698 2877903997293017826999469 := by
  unfold tailWord_5604698
  simp only [CollatzResearch.WordTrace]
  refine ⟨51105032462285956764107687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136280086566095884704287165 51105032462285956764107687)
  ·
    refine ⟨76657548693428935146161531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51105032462285956764107687 76657548693428935146161531)
    ·
      refine ⟨114986323040143402719242297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76657548693428935146161531 114986323040143402719242297)
      ·
        refine ⟨86239742280107552039431723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114986323040143402719242297 86239742280107552039431723)
        ·
          refine ⟨129359613420161328059147585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86239742280107552039431723 129359613420161328059147585)
          ·
            refine ⟨97019710065120996044360689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129359613420161328059147585 97019710065120996044360689)
            ·
              refine ⟨72764782548840747033270517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97019710065120996044360689 72764782548840747033270517)
              ·
                refine ⟨6821698363953820034369111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72764782548840747033270517 6821698363953820034369111)
                ·
                  refine ⟨10232547545930730051553667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6821698363953820034369111 10232547545930730051553667)
                  ·
                    refine ⟨15348821318896095077330501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10232547545930730051553667 15348821318896095077330501)
                    ·
                      refine ⟨2877903997293017826999469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15348821318896095077330501 2877903997293017826999469)
                      ·
                        rfl

theorem cell23_5604698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_5604698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604698 prefixEnd_5604698 := by exact prefixLift 5604698
  have htrace : WordTrace (prefixWord ++ tailWord_5604698) baseStart_5604698 baseEnd_5604698 := by
    simpa [prefixWord, tailWord_5604698, baseEnd_5604698] using wordTrace_append hprefix tailTrace_5604698
  have hstable : (prefixWord ++ tailWord_5604698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604698).length < 2 ^ (prefixWord ++ tailWord_5604698).sum := by decide
  have hdescent : baseEnd_5604698 < baseStart_5604698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604721 : List Nat := [1, 2, 2, 2, 1, 2, 5, 8]
def baseStart_5604721 : Nat := 118140960795 + 5604721 * 2 ^ 59
def prefixEnd_5604721 : Nat := 4983230072969 + 3 ^ 40 * 5604721 * 2
def baseEnd_5604721 : Nat := 106589474346224860630069

theorem tailTrace_5604721 : CollatzResearch.WordTrace tailWord_5604721 prefixEnd_5604721 106589474346224860630069 := by
  unfold tailWord_5604721
  simp only [CollatzResearch.WordTrace]
  refine ⟨204420968728060501984518017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136280645818707001323012011 204420968728060501984518017)
  ·
    refine ⟨153315726546045376488388513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204420968728060501984518017 153315726546045376488388513)
    ·
      refine ⟨114986794909534032366291385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153315726546045376488388513 114986794909534032366291385)
      ·
        refine ⟨86240096182150524274718539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114986794909534032366291385 86240096182150524274718539)
        ·
          refine ⟨129360144273225786412077809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86240096182150524274718539 129360144273225786412077809)
          ·
            refine ⟨97020108204919339809058357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129360144273225786412077809 97020108204919339809058357)
            ·
              refine ⟨9095635144211188107099221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97020108204919339809058357 9095635144211188107099221)
              ·
                refine ⟨106589474346224860630069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9095635144211188107099221 106589474346224860630069)
                ·
                  rfl

theorem cell23_5604721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 8].length) (baseStart_5604721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604721 prefixEnd_5604721 := by exact prefixLift 5604721
  have htrace : WordTrace (prefixWord ++ tailWord_5604721) baseStart_5604721 baseEnd_5604721 := by
    simpa [prefixWord, tailWord_5604721, baseEnd_5604721] using wordTrace_append hprefix tailTrace_5604721
  have hstable : (prefixWord ++ tailWord_5604721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604721).length < 2 ^ (prefixWord ++ tailWord_5604721).sum := by decide
  have hdescent : baseEnd_5604721 < baseStart_5604721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604725 : List Nat := [1, 3, 4, 1, 3, 1, 2, 1, 1, 6]
def baseStart_5604725 : Nat := 118140960795 + 5604725 * 2 ^ 59
def prefixEnd_5604725 : Nat := 4983230072969 + 3 ^ 40 * 5604725 * 2
def baseEnd_5604725 : Nat := 959305953756896407120615

theorem tailTrace_5604725 : CollatzResearch.WordTrace tailWord_5604725 prefixEnd_5604725 959305953756896407120615 := by
  unfold tailWord_5604725
  simp only [CollatzResearch.WordTrace]
  refine ⟨204421114620046010667663629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136280743080030673778442419 204421114620046010667663629)
  ·
    refine ⟨76657917982517254000373861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204421114620046010667663629 76657917982517254000373861)
    ·
      refine ⟨14373359621721985125070099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76657917982517254000373861 14373359621721985125070099)
      ·
        refine ⟨21560039432582977687605149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14373359621721985125070099 21560039432582977687605149)
        ·
          refine ⟨8085014787218616632851931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21560039432582977687605149 8085014787218616632851931)
          ·
            refine ⟨12127522180827924949277897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8085014787218616632851931 12127522180827924949277897)
            ·
              refine ⟨9095641635620943711958423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12127522180827924949277897 9095641635620943711958423)
              ·
                refine ⟨13643462453431415567937635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9095641635620943711958423 13643462453431415567937635)
                ·
                  refine ⟨20465193680147123351906453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13643462453431415567937635 20465193680147123351906453)
                  ·
                    refine ⟨959305953756896407120615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20465193680147123351906453 959305953756896407120615)
                    ·
                      rfl

theorem cell23_5604725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_5604725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604725 prefixEnd_5604725 := by exact prefixLift 5604725
  have htrace : WordTrace (prefixWord ++ tailWord_5604725) baseStart_5604725 baseEnd_5604725 := by
    simpa [prefixWord, tailWord_5604725, baseEnd_5604725] using wordTrace_append hprefix tailTrace_5604725
  have hstable : (prefixWord ++ tailWord_5604725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604725).length < 2 ^ (prefixWord ++ tailWord_5604725).sum := by decide
  have hdescent : baseEnd_5604725 < baseStart_5604725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604748 : List Nat := [2, 2, 1, 2, 1, 3, 1, 4, 1, 3, 3]
def baseStart_5604748 : Nat := 118140960795 + 5604748 * 2 ^ 59
def prefixEnd_5604748 : Nat := 4983230072969 + 3 ^ 40 * 5604748 * 2
def baseEnd_5604748 : Nat := 2877929671325742631374239

theorem tailTrace_5604748 : CollatzResearch.WordTrace tailWord_5604748 prefixEnd_5604748 2877929671325742631374239 := by
  unfold tailWord_5604748
  simp only [CollatzResearch.WordTrace]
  refine ⟨102210976749481342797875449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136281302332641790397167265 102210976749481342797875449)
  ·
    refine ⟨76658232562111007098406587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102210976749481342797875449 76658232562111007098406587)
    ·
      refine ⟨114987348843166510647609881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76658232562111007098406587 114987348843166510647609881)
      ·
        refine ⟨86240511632374882985707411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114987348843166510647609881 86240511632374882985707411)
        ·
          refine ⟨129360767448562324478561117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86240511632374882985707411 129360767448562324478561117)
          ·
            refine ⟨48510287793210871679460419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129360767448562324478561117 48510287793210871679460419)
            ·
              refine ⟨72765431689816307519190629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48510287793210871679460419 72765431689816307519190629)
              ·
                refine ⟨13643518441840557659848243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72765431689816307519190629 13643518441840557659848243)
                ·
                  refine ⟨20465277662760836489772365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13643518441840557659848243 20465277662760836489772365)
                  ·
                    refine ⟨7674479123535313683664637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20465277662760836489772365 7674479123535313683664637)
                    ·
                      refine ⟨2877929671325742631374239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7674479123535313683664637 2877929671325742631374239)
                      ·
                        rfl

theorem cell23_5604748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_5604748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604748 prefixEnd_5604748 := by exact prefixLift 5604748
  have htrace : WordTrace (prefixWord ++ tailWord_5604748) baseStart_5604748 baseEnd_5604748 := by
    simpa [prefixWord, tailWord_5604748, baseEnd_5604748] using wordTrace_append hprefix tailTrace_5604748
  have hstable : (prefixWord ++ tailWord_5604748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604748).length < 2 ^ (prefixWord ++ tailWord_5604748).sum := by decide
  have hdescent : baseEnd_5604748 < baseStart_5604748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604766 : List Nat := [4, 3, 1, 2, 2, 1, 2, 1, 3, 2, 2]
def baseStart_5604766 : Nat := 118140960795 + 5604766 * 2 ^ 59
def prefixEnd_5604766 : Nat := 4983230072969 + 3 ^ 40 * 5604766 * 2
def baseEnd_5604766 : Nat := 2877938913977523560949157

theorem tailTrace_5604766 : CollatzResearch.WordTrace tailWord_5604766 prefixEnd_5604766 2877938913977523560949157 := by
  unfold tailWord_5604766
  simp only [CollatzResearch.WordTrace]
  refine ⟨25552826251612184333738269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136281740008598316446604101 25552826251612184333738269)
  ·
    refine ⟨9582309844354569125151851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25552826251612184333738269 9582309844354569125151851)
    ·
      refine ⟨14373464766531853687727777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9582309844354569125151851 14373464766531853687727777)
      ·
        refine ⟨10780098574898890265795833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14373464766531853687727777 10780098574898890265795833)
        ·
          refine ⟨8085073931174167699346875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10780098574898890265795833 8085073931174167699346875)
          ·
            refine ⟨12127610896761251549020313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8085073931174167699346875 12127610896761251549020313)
            ·
              refine ⟨9095708172570938661765235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12127610896761251549020313 9095708172570938661765235)
              ·
                refine ⟨13643562258856407992647853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9095708172570938661765235 13643562258856407992647853)
                ·
                  refine ⟨5116335847071152997242945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13643562258856407992647853 5116335847071152997242945)
                  ·
                    refine ⟨3837251885303364747932209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5116335847071152997242945 3837251885303364747932209)
                    ·
                      refine ⟨2877938913977523560949157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3837251885303364747932209 2877938913977523560949157)
                      ·
                        rfl

theorem cell23_5604766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_5604766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604766 prefixEnd_5604766 := by exact prefixLift 5604766
  have htrace : WordTrace (prefixWord ++ tailWord_5604766) baseStart_5604766 baseEnd_5604766 := by
    simpa [prefixWord, tailWord_5604766, baseEnd_5604766] using wordTrace_append hprefix tailTrace_5604766
  have hstable : (prefixWord ++ tailWord_5604766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604766).length < 2 ^ (prefixWord ++ tailWord_5604766).sum := by decide
  have hdescent : baseEnd_5604766 < baseStart_5604766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604808 : List Nat := [2, 1, 3, 1, 3, 1, 3, 1, 2, 1, 5]
def baseStart_5604808 : Nat := 118140960795 + 5604808 * 2 ^ 59
def prefixEnd_5604808 : Nat := 4983230072969 + 3 ^ 40 * 5604808 * 2
def baseEnd_5604808 : Nat := 2877960480165012396623963

theorem tailTrace_5604808 : CollatzResearch.WordTrace tailWord_5604808 prefixEnd_5604808 2877960480165012396623963 := by
  unfold tailWord_5604808
  simp only [CollatzResearch.WordTrace]
  refine ⟨102212070939372657921467539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136282761252496877228623385 102212070939372657921467539)
  ·
    refine ⟨153318106409058986882201309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102212070939372657921467539 153318106409058986882201309)
    ·
      refine ⟨57494289903397120080825491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153318106409058986882201309 57494289903397120080825491)
      ·
        refine ⟨86241434855095680121238237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57494289903397120080825491 86241434855095680121238237)
        ·
          refine ⟨32340538070660880045464339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86241434855095680121238237 32340538070660880045464339)
          ·
            refine ⟨48510807105991320068196509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32340538070660880045464339 48510807105991320068196509)
            ·
              refine ⟨18191552664746745025573691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48510807105991320068196509 18191552664746745025573691)
              ·
                refine ⟨27287328997120117538360537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18191552664746745025573691 27287328997120117538360537)
                ·
                  refine ⟨20465496747840088153770403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27287328997120117538360537 20465496747840088153770403)
                  ·
                    refine ⟨30698245121760132230655605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20465496747840088153770403 30698245121760132230655605)
                    ·
                      refine ⟨2877960480165012396623963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30698245121760132230655605 2877960480165012396623963)
                      ·
                        rfl

theorem cell23_5604808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_5604808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604808 prefixEnd_5604808 := by exact prefixLift 5604808
  have htrace : WordTrace (prefixWord ++ tailWord_5604808) baseStart_5604808 baseEnd_5604808 := by
    simpa [prefixWord, tailWord_5604808, baseEnd_5604808] using wordTrace_append hprefix tailTrace_5604808
  have hstable : (prefixWord ++ tailWord_5604808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604808).length < 2 ^ (prefixWord ++ tailWord_5604808).sum := by decide
  have hdescent : baseEnd_5604808 < baseStart_5604808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604811 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 9]
def baseStart_5604811 : Nat := 118140960795 + 5604811 * 2 ^ 59
def prefixEnd_5604811 : Nat := 4983230072969 + 3 ^ 40 * 5604811 * 2
def baseEnd_5604811 : Nat := 319773557845219542765161

theorem tailTrace_5604811 : CollatzResearch.WordTrace tailWord_5604811 prefixEnd_5604811 319773557845219542765161 := by
  unfold tailWord_5604811
  simp only [CollatzResearch.WordTrace]
  refine ⟨204424251297734447355294287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136282834198489631570196191 204424251297734447355294287)
  ·
    refine ⟨306636376946601671032941431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204424251297734447355294287 306636376946601671032941431)
    ·
      refine ⟨459954565419902506549412147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306636376946601671032941431 459954565419902506549412147)
      ·
        refine ⟨689931848129853759824118221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459954565419902506549412147 689931848129853759824118221)
        ·
          refine ⟨258724443048695159934044333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 689931848129853759824118221 258724443048695159934044333)
          ·
            refine ⟨97021666143260684975266625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 258724443048695159934044333 97021666143260684975266625)
            ·
              refine ⟨72766249607445513731449969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97021666143260684975266625 72766249607445513731449969)
              ·
                refine ⟨54574687205584135298587477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72766249607445513731449969 54574687205584135298587477)
                ·
                  refine ⟨319773557845219542765161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54574687205584135298587477 319773557845219542765161)
                  ·
                    rfl

theorem cell23_5604811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 9].length) (baseStart_5604811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604811 prefixEnd_5604811 := by exact prefixLift 5604811
  have htrace : WordTrace (prefixWord ++ tailWord_5604811) baseStart_5604811 baseEnd_5604811 := by
    simpa [prefixWord, tailWord_5604811, baseEnd_5604811] using wordTrace_append hprefix tailTrace_5604811
  have hstable : (prefixWord ++ tailWord_5604811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604811).length < 2 ^ (prefixWord ++ tailWord_5604811).sum := by decide
  have hdescent : baseEnd_5604811 < baseStart_5604811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604839 : List Nat := [1, 1, 5, 2, 1, 3, 1, 3, 2, 2, 2]
def baseStart_5604839 : Nat := 118140960795 + 5604839 * 2 ^ 59
def prefixEnd_5604839 : Nat := 4983230072969 + 3 ^ 40 * 5604839 * 2
def baseEnd_5604839 : Nat := 2877976398065301775336321

theorem tailTrace_5604839 : CollatzResearch.WordTrace tailWord_5604839 prefixEnd_5604839 2877976398065301775336321 := by
  unfold tailWord_5604839
  simp only [CollatzResearch.WordTrace]
  refine ⟨204425272541633008137313571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136283515027755338758209047 204425272541633008137313571)
  ·
    refine ⟨306637908812449512205970357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204425272541633008137313571 306637908812449512205970357)
    ·
      refine ⟨28747303951167141769309721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 306637908812449512205970357 28747303951167141769309721)
      ·
        refine ⟨21560477963375356326982291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28747303951167141769309721 21560477963375356326982291)
        ·
          refine ⟨32340716945063034490473437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21560477963375356326982291 32340716945063034490473437)
          ·
            refine ⟨12127768854398637933927539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32340716945063034490473437 12127768854398637933927539)
            ·
              refine ⟨18191653281597956900891309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12127768854398637933927539 18191653281597956900891309)
              ·
                refine ⟨6821869980599233837834241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18191653281597956900891309 6821869980599233837834241)
                ·
                  refine ⟨5116402485449425378375681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6821869980599233837834241 5116402485449425378375681)
                  ·
                    refine ⟨3837301864087069033781761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5116402485449425378375681 3837301864087069033781761)
                    ·
                      refine ⟨2877976398065301775336321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3837301864087069033781761 2877976398065301775336321)
                      ·
                        rfl

theorem cell23_5604839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_5604839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604839 prefixEnd_5604839 := by exact prefixLift 5604839
  have htrace : WordTrace (prefixWord ++ tailWord_5604839) baseStart_5604839 baseEnd_5604839 := by
    simpa [prefixWord, tailWord_5604839, baseEnd_5604839] using wordTrace_append hprefix tailTrace_5604839
  have hstable : (prefixWord ++ tailWord_5604839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604839).length < 2 ^ (prefixWord ++ tailWord_5604839).sum := by decide
  have hdescent : baseEnd_5604839 < baseStart_5604839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604895 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 1, 6, 2]
def baseStart_5604895 : Nat := 118140960795 + 5604895 * 2 ^ 59
def prefixEnd_5604895 : Nat := 4983230072969 + 3 ^ 40 * 5604895 * 2
def baseEnd_5604895 : Nat := 2878005152981953556236063

theorem tailTrace_5604895 : CollatzResearch.WordTrace tailWord_5604895 prefixEnd_5604895 2878005152981953556236063 := by
  unfold tailWord_5604895
  simp only [CollatzResearch.WordTrace]
  refine ⟨204427315029430129701352139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136284876686286753134234759 204427315029430129701352139)
  ·
    refine ⟨306640972544145194552028209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204427315029430129701352139 306640972544145194552028209)
    ·
      refine ⟨229980729408108895914021157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306640972544145194552028209 229980729408108895914021157)
      ·
        refine ⟨43121386764020417983878967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 229980729408108895914021157 43121386764020417983878967)
        ·
          refine ⟨64682080146030626975818451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43121386764020417983878967 64682080146030626975818451)
          ·
            refine ⟨97023120219045940463727677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64682080146030626975818451 97023120219045940463727677)
            ·
              refine ⟨36383670082142227673897879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97023120219045940463727677 36383670082142227673897879)
              ·
                refine ⟨54575505123213341510846819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36383670082142227673897879 54575505123213341510846819)
                ·
                  refine ⟨81863257684820012266270229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54575505123213341510846819 81863257684820012266270229)
                  ·
                    refine ⟨3837340203975938074981417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81863257684820012266270229 3837340203975938074981417)
                    ·
                      refine ⟨2878005152981953556236063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3837340203975938074981417 2878005152981953556236063)
                      ·
                        rfl

theorem cell23_5604895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_5604895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604895 prefixEnd_5604895 := by exact prefixLift 5604895
  have htrace : WordTrace (prefixWord ++ tailWord_5604895) baseStart_5604895 baseEnd_5604895 := by
    simpa [prefixWord, tailWord_5604895, baseEnd_5604895] using wordTrace_append hprefix tailTrace_5604895
  have hstable : (prefixWord ++ tailWord_5604895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604895).length < 2 ^ (prefixWord ++ tailWord_5604895).sum := by decide
  have hdescent : baseEnd_5604895 < baseStart_5604895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604915 : List Nat := [1, 1, 1, 2, 4, 4, 1, 1, 1, 4, 3]
def baseStart_5604915 : Nat := 118140960795 + 5604915 * 2 ^ 59
def prefixEnd_5604915 : Nat := 4983230072969 + 3 ^ 40 * 5604915 * 2
def baseEnd_5604915 : Nat := 2878015422595043477985971

theorem tailTrace_5604915 : CollatzResearch.WordTrace tailWord_5604915 prefixEnd_5604915 2878015422595043477985971 := by
  unfold tailWord_5604915
  simp only [CollatzResearch.WordTrace]
  refine ⟨204428044489357673117080199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136285362992905115411386799 204428044489357673117080199)
  ·
    refine ⟨306642066734036509675620299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204428044489357673117080199 306642066734036509675620299)
    ·
      refine ⟨459963100101054764513430449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306642066734036509675620299 459963100101054764513430449)
      ·
        refine ⟨344972325075791073385072837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 459963100101054764513430449 344972325075791073385072837)
        ·
          refine ⟨64682310951710826259701157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 344972325075791073385072837 64682310951710826259701157)
          ·
            refine ⟨12127933303445779923693967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64682310951710826259701157 12127933303445779923693967)
            ·
              refine ⟨18191899955168669885540951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12127933303445779923693967 18191899955168669885540951)
              ·
                refine ⟨27287849932753004828311427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18191899955168669885540951 27287849932753004828311427)
                ·
                  refine ⟨40931774899129507242467141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27287849932753004828311427 40931774899129507242467141)
                  ·
                    refine ⟨7674707793586782607962589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40931774899129507242467141 7674707793586782607962589)
                    ·
                      refine ⟨2878015422595043477985971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7674707793586782607962589 2878015422595043477985971)
                      ·
                        rfl

theorem cell23_5604915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 4, 3].length) (baseStart_5604915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604915 prefixEnd_5604915 := by exact prefixLift 5604915
  have htrace : WordTrace (prefixWord ++ tailWord_5604915) baseStart_5604915 baseEnd_5604915 := by
    simpa [prefixWord, tailWord_5604915, baseEnd_5604915] using wordTrace_append hprefix tailTrace_5604915
  have hstable : (prefixWord ++ tailWord_5604915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604915).length < 2 ^ (prefixWord ++ tailWord_5604915).sum := by decide
  have hdescent : baseEnd_5604915 < baseStart_5604915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604935 : List Nat := [1, 1, 4, 1, 5, 1, 1, 1, 8]
def baseStart_5604935 : Nat := 118140960795 + 5604935 * 2 ^ 59
def prefixEnd_5604935 : Nat := 4983230072969 + 3 ^ 40 * 5604935 * 2
def baseEnd_5604935 : Nat := 319780632467570377748431

theorem tailTrace_5604935 : CollatzResearch.WordTrace tailWord_5604935 prefixEnd_5604935 319780632467570377748431 := by
  unfold tailWord_5604935
  simp only [CollatzResearch.WordTrace]
  refine ⟨204428773949285216532808259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136285849299523477688538839 204428773949285216532808259)
  ·
    refine ⟨306643160923927824799212389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204428773949285216532808259 306643160923927824799212389)
    ·
      refine ⟨57495592673236467149852323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 306643160923927824799212389 57495592673236467149852323)
      ·
        refine ⟨86243389009854700724778485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57495592673236467149852323 86243389009854700724778485)
        ·
          refine ⟨8085317719673878192947983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86243389009854700724778485 8085317719673878192947983)
          ·
            refine ⟨12127976579510817289421975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8085317719673878192947983 12127976579510817289421975)
            ·
              refine ⟨18191964869266225934132963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12127976579510817289421975 18191964869266225934132963)
              ·
                refine ⟨27287947303899338901199445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18191964869266225934132963 27287947303899338901199445)
                ·
                  refine ⟨319780632467570377748431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27287947303899338901199445 319780632467570377748431)
                  ·
                    rfl

theorem cell23_5604935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 8].length) (baseStart_5604935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604935 prefixEnd_5604935 := by exact prefixLift 5604935
  have htrace : WordTrace (prefixWord ++ tailWord_5604935) baseStart_5604935 baseEnd_5604935 := by
    simpa [prefixWord, tailWord_5604935, baseEnd_5604935] using wordTrace_append hprefix tailTrace_5604935
  have hstable : (prefixWord ++ tailWord_5604935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604935).length < 2 ^ (prefixWord ++ tailWord_5604935).sum := by decide
  have hdescent : baseEnd_5604935 < baseStart_5604935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604938 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 1, 1, 8]
def baseStart_5604938 : Nat := 118140960795 + 5604938 * 2 ^ 59
def prefixEnd_5604938 : Nat := 4983230072969 + 3 ^ 40 * 5604938 * 2
def baseEnd_5604938 : Nat := 2878027232650096887998365

theorem tailTrace_5604938 : CollatzResearch.WordTrace tailWord_5604938 prefixEnd_5604938 2878027232650096887998365 := by
  unfold tailWord_5604938
  simp only [CollatzResearch.WordTrace]
  refine ⟨51107220842068587011291867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136285922245516232030111645 51107220842068587011291867)
  ·
    refine ⟨76660831263102880516937801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51107220842068587011291867 76660831263102880516937801)
    ·
      refine ⟨57495623447327160387703351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76660831263102880516937801 57495623447327160387703351)
      ·
        refine ⟨86243435170990740581555027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57495623447327160387703351 86243435170990740581555027)
        ·
          refine ⟨129365152756486110872332541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86243435170990740581555027 129365152756486110872332541)
          ·
            refine ⟨48511932283682291577124703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129365152756486110872332541 48511932283682291577124703)
            ·
              refine ⟨72767898425523437365687055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48511932283682291577124703 72767898425523437365687055)
              ·
                refine ⟨109151847638285156048530583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72767898425523437365687055 109151847638285156048530583)
                ·
                  refine ⟨163727771457427734072795875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109151847638285156048530583 163727771457427734072795875)
                  ·
                    refine ⟨245591657186141601109193813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 163727771457427734072795875 245591657186141601109193813)
                    ·
                      refine ⟨2878027232650096887998365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 245591657186141601109193813 2878027232650096887998365)
                      ·
                        rfl

theorem cell23_5604938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_5604938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604938 prefixEnd_5604938 := by exact prefixLift 5604938
  have htrace : WordTrace (prefixWord ++ tailWord_5604938) baseStart_5604938 baseEnd_5604938 := by
    simpa [prefixWord, tailWord_5604938, baseEnd_5604938] using wordTrace_append hprefix tailTrace_5604938
  have hstable : (prefixWord ++ tailWord_5604938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604938).length < 2 ^ (prefixWord ++ tailWord_5604938).sum := by decide
  have hdescent : baseEnd_5604938 < baseStart_5604938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604972 : List Nat := [2, 2, 1, 1, 3, 1, 1, 5, 2, 3, 2]
def baseStart_5604972 : Nat := 118140960795 + 5604972 * 2 ^ 59
def prefixEnd_5604972 : Nat := 4983230072969 + 3 ^ 40 * 5604972 * 2
def baseEnd_5604972 : Nat := 2878044690992349754973209

theorem tailTrace_5604972 : CollatzResearch.WordTrace tailWord_5604972 prefixEnd_5604972 2878044690992349754973209 := by
  unfold tailWord_5604972
  simp only [CollatzResearch.WordTrace]
  refine ⟨102215061725075585925952585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136286748966767447901270113 102215061725075585925952585)
  ·
    refine ⟨76661296293806689444464439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102215061725075585925952585 76661296293806689444464439)
    ·
      refine ⟨114991944440710034166696659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76661296293806689444464439 114991944440710034166696659)
      ·
        refine ⟨172487916661065051250044989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114991944440710034166696659 172487916661065051250044989)
        ·
          refine ⟨64682968747899394218766871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172487916661065051250044989 64682968747899394218766871)
          ·
            refine ⟨97024453121849091328150307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64682968747899394218766871 97024453121849091328150307)
            ·
              refine ⟨145536679682773636992225461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97024453121849091328150307 145536679682773636992225461)
              ·
                refine ⟨13644063720260028468021137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145536679682773636992225461 13644063720260028468021137)
                ·
                  refine ⟨10233047790195021351015853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13644063720260028468021137 10233047790195021351015853)
                  ·
                    refine ⟨3837392921323133006630945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10233047790195021351015853 3837392921323133006630945)
                    ·
                      refine ⟨2878044690992349754973209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3837392921323133006630945 2878044690992349754973209)
                      ·
                        rfl

theorem cell23_5604972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 3, 2].length) (baseStart_5604972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604972 prefixEnd_5604972 := by exact prefixLift 5604972
  have htrace : WordTrace (prefixWord ++ tailWord_5604972) baseStart_5604972 baseEnd_5604972 := by
    simpa [prefixWord, tailWord_5604972, baseEnd_5604972] using wordTrace_append hprefix tailTrace_5604972
  have hstable : (prefixWord ++ tailWord_5604972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604972).length < 2 ^ (prefixWord ++ tailWord_5604972).sum := by decide
  have hdescent : baseEnd_5604972 < baseStart_5604972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604973 : List Nat := [1, 5, 1, 1, 5, 1, 1, 3, 1, 4]
def baseStart_5604973 : Nat := 118140960795 + 5604973 * 2 ^ 59
def prefixEnd_5604973 : Nat := 4983230072969 + 3 ^ 40 * 5604973 * 2
def baseEnd_5604973 : Nat := 959348401491001417020235

theorem tailTrace_5604973 : CollatzResearch.WordTrace tailWord_5604973 prefixEnd_5604973 959348401491001417020235 := by
  unfold tailWord_5604973
  simp only [CollatzResearch.WordTrace]
  refine ⟨204430159923147549022691573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136286773282098366015127715 204430159923147549022691573)
  ·
    refine ⟨19165327492795082720877335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 204430159923147549022691573 19165327492795082720877335)
    ·
      refine ⟨28747991239192624081316003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19165327492795082720877335 28747991239192624081316003)
      ·
        refine ⟨43121986858788936121974005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28747991239192624081316003 43121986858788936121974005)
        ·
          refine ⟨4042686268011462761435063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43121986858788936121974005 4042686268011462761435063)
          ·
            refine ⟨6064029402017194142152595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4042686268011462761435063 6064029402017194142152595)
            ·
              refine ⟨9096044103025791213228893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6064029402017194142152595 9096044103025791213228893)
              ·
                refine ⟨3411016538634671704960835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9096044103025791213228893 3411016538634671704960835)
                ·
                  refine ⟨5116524807952007557441253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3411016538634671704960835 5116524807952007557441253)
                  ·
                    refine ⟨959348401491001417020235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5116524807952007557441253 959348401491001417020235)
                    ·
                      rfl

theorem cell23_5604973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_5604973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604973 prefixEnd_5604973 := by exact prefixLift 5604973
  have htrace : WordTrace (prefixWord ++ tailWord_5604973) baseStart_5604973 baseEnd_5604973 := by
    simpa [prefixWord, tailWord_5604973, baseEnd_5604973] using wordTrace_append hprefix tailTrace_5604973
  have hstable : (prefixWord ++ tailWord_5604973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604973).length < 2 ^ (prefixWord ++ tailWord_5604973).sum := by decide
  have hdescent : baseEnd_5604973 < baseStart_5604973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604989 : List Nat := [1, 4, 1, 1, 4, 2, 1, 2, 2, 3, 2]
def baseStart_5604989 : Nat := 118140960795 + 5604989 * 2 ^ 59
def prefixEnd_5604989 : Nat := 4983230072969 + 3 ^ 40 * 5604989 * 2
def baseEnd_5604989 : Nat := 2878053420163476188460631

theorem tailTrace_5604989 : CollatzResearch.WordTrace tailWord_5604989 prefixEnd_5604989 2878053420163476188460631 := by
  unfold tailWord_5604989
  simp only [CollatzResearch.WordTrace]
  refine ⟨204430743491089583755274021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136287162327393055836849347 204430743491089583755274021)
  ·
    refine ⟨38330764404579296954113879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204430743491089583755274021 38330764404579296954113879)
    ·
      refine ⟨57496146606868945431170819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38330764404579296954113879 57496146606868945431170819)
      ·
        refine ⟨86244219910303418146756229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57496146606868945431170819 86244219910303418146756229)
        ·
          refine ⟨16170791233181890902516793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86244219910303418146756229 16170791233181890902516793)
          ·
            refine ⟨12128093424886418176887595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16170791233181890902516793 12128093424886418176887595)
            ·
              refine ⟨18192140137329627265331393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12128093424886418176887595 18192140137329627265331393)
              ·
                refine ⟨13644105102997220448998545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18192140137329627265331393 13644105102997220448998545)
                ·
                  refine ⟨10233078827247915336748909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13644105102997220448998545 10233078827247915336748909)
                  ·
                    refine ⟨3837404560217968251280841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10233078827247915336748909 3837404560217968251280841)
                    ·
                      refine ⟨2878053420163476188460631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3837404560217968251280841 2878053420163476188460631)
                      ·
                        rfl

theorem cell23_5604989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 3, 2].length) (baseStart_5604989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604989 prefixEnd_5604989 := by exact prefixLift 5604989
  have htrace : WordTrace (prefixWord ++ tailWord_5604989) baseStart_5604989 baseEnd_5604989 := by
    simpa [prefixWord, tailWord_5604989, baseEnd_5604989] using wordTrace_append hprefix tailTrace_5604989
  have hstable : (prefixWord ++ tailWord_5604989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604989).length < 2 ^ (prefixWord ++ tailWord_5604989).sum := by decide
  have hdescent : baseEnd_5604989 < baseStart_5604989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5604996 : List Nat := [2, 3, 2, 1, 4, 2, 1, 1, 3, 1, 3]
def baseStart_5604996 : Nat := 118140960795 + 5604996 * 2 ^ 59
def prefixEnd_5604996 : Nat := 4983230072969 + 3 ^ 40 * 5604996 * 2
def baseEnd_5604996 : Nat := 2878057014528057661073099

theorem tailTrace_5604996 : CollatzResearch.WordTrace tailWord_5604996 prefixEnd_5604996 2878057014528057661073099 := by
  unfold tailWord_5604996
  simp only [CollatzResearch.WordTrace]
  refine ⟨102215499401032111975389421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136287332534709482633852561 102215499401032111975389421)
  ·
    refine ⟨38330812275387041990771033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102215499401032111975389421 38330812275387041990771033)
    ·
      refine ⟨28748109206540281493078275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38330812275387041990771033 28748109206540281493078275)
      ·
        refine ⟨43122163809810422239617413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28748109206540281493078275 43122163809810422239617413)
        ·
          refine ⟨8085405714339454169928265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43122163809810422239617413 8085405714339454169928265)
          ·
            refine ⟨6064054285754590627446199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8085405714339454169928265 6064054285754590627446199)
            ·
              refine ⟨9096081428631885941169299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6064054285754590627446199 9096081428631885941169299)
              ·
                refine ⟨13644122142947828911753949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9096081428631885941169299 13644122142947828911753949)
                ·
                  refine ⟨5116545803605435841907731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13644122142947828911753949 5116545803605435841907731)
                  ·
                    refine ⟨7674818705408153762861597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5116545803605435841907731 7674818705408153762861597)
                    ·
                      refine ⟨2878057014528057661073099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7674818705408153762861597 2878057014528057661073099)
                      ·
                        rfl

theorem cell23_5604996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_5604996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5604996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5604996 prefixEnd_5604996 := by exact prefixLift 5604996
  have htrace : WordTrace (prefixWord ++ tailWord_5604996) baseStart_5604996 baseEnd_5604996 := by
    simpa [prefixWord, tailWord_5604996, baseEnd_5604996] using wordTrace_append hprefix tailTrace_5604996
  have hstable : (prefixWord ++ tailWord_5604996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5604996).length < 2 ^ (prefixWord ++ tailWord_5604996).sum := by decide
  have hdescent : baseEnd_5604996 < baseStart_5604996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5604996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605015 : List Nat := [1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 6]
def baseStart_5605015 : Nat := 118140960795 + 5605015 * 2 ^ 59
def prefixEnd_5605015 : Nat := 4983230072969 + 3 ^ 40 * 5605015 * 2
def baseEnd_5605015 : Nat := 2878066770660493086735511

theorem tailTrace_5605015 : CollatzResearch.WordTrace tailWord_5605015 prefixEnd_5605015 2878066770660493086735511 := by
  unfold tailWord_5605015
  simp only [CollatzResearch.WordTrace]
  refine ⟨204431691788995390195720499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136287794525996926797146999 204431691788995390195720499)
  ·
    refine ⟨306647537683493085293580749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204431691788995390195720499 306647537683493085293580749)
    ·
      refine ⟨114992826631309906985092781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306647537683493085293580749 114992826631309906985092781)
      ·
        refine ⟨43122309986741215119409793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114992826631309906985092781 43122309986741215119409793)
        ·
          refine ⟨32341732490055911339557345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43122309986741215119409793 32341732490055911339557345)
          ·
            refine ⟨24256299367541933504668009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32341732490055911339557345 24256299367541933504668009)
            ·
              refine ⟨18192224525656450128501007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24256299367541933504668009 18192224525656450128501007)
              ·
                refine ⟨27288336788484675192751511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18192224525656450128501007 27288336788484675192751511)
                ·
                  refine ⟨40932505182727012789127267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27288336788484675192751511 40932505182727012789127267)
                  ·
                    refine ⟨61398757774090519183690901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40932505182727012789127267 61398757774090519183690901)
                    ·
                      refine ⟨2878066770660493086735511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61398757774090519183690901 2878066770660493086735511)
                      ·
                        rfl

theorem cell23_5605015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_5605015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605015 prefixEnd_5605015 := by exact prefixLift 5605015
  have htrace : WordTrace (prefixWord ++ tailWord_5605015) baseStart_5605015 baseEnd_5605015 := by
    simpa [prefixWord, tailWord_5605015, baseEnd_5605015] using wordTrace_append hprefix tailTrace_5605015
  have hstable : (prefixWord ++ tailWord_5605015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605015).length < 2 ^ (prefixWord ++ tailWord_5605015).sum := by decide
  have hdescent : baseEnd_5605015 < baseStart_5605015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605025 : List Nat := [1, 2, 3, 3, 2, 1, 2, 9]
def baseStart_5605025 : Nat := 118140960795 + 5605025 * 2 ^ 59
def prefixEnd_5605025 : Nat := 4983230072969 + 3 ^ 40 * 5605025 * 2
def baseEnd_5605025 : Nat := 106595255758038446207795

theorem tailTrace_5605025 : CollatzResearch.WordTrace tailWord_5605025 prefixEnd_5605025 106595255758038446207795 := by
  unfold tailWord_5605025
  simp only [CollatzResearch.WordTrace]
  refine ⟨204432056518959161903584529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136288037679306107935723019 204432056518959161903584529)
  ·
    refine ⟨153324042389219371427688397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204432056518959161903584529 153324042389219371427688397)
    ·
      refine ⟨57496515895957264285383149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153324042389219371427688397 57496515895957264285383149)
      ·
        refine ⟨21561193460983974107018681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57496515895957264285383149 21561193460983974107018681)
        ·
          refine ⟨16170895095737980580264011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21561193460983974107018681 16170895095737980580264011)
          ·
            refine ⟨24256342643606970870396017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16170895095737980580264011 24256342643606970870396017)
            ·
              refine ⟨18192256982705228152797013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24256342643606970870396017 18192256982705228152797013)
              ·
                refine ⟨106595255758038446207795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18192256982705228152797013 106595255758038446207795)
                ·
                  rfl

theorem cell23_5605025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 9].length) (baseStart_5605025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605025 prefixEnd_5605025 := by exact prefixLift 5605025
  have htrace : WordTrace (prefixWord ++ tailWord_5605025) baseStart_5605025 baseEnd_5605025 := by
    simpa [prefixWord, tailWord_5605025, baseEnd_5605025] using wordTrace_append hprefix tailTrace_5605025
  have hstable : (prefixWord ++ tailWord_5605025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605025).length < 2 ^ (prefixWord ++ tailWord_5605025).sum := by decide
  have hdescent : baseEnd_5605025 < baseStart_5605025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605039 : List Nat := [1, 1, 2, 1, 2, 4, 5, 1, 1, 2, 3]
def baseStart_5605039 : Nat := 118140960795 + 5605039 * 2 ^ 59
def prefixEnd_5605039 : Nat := 4983230072969 + 3 ^ 40 * 5605039 * 2
def baseEnd_5605039 : Nat := 2878079094196200992835401

theorem tailTrace_5605039 : CollatzResearch.WordTrace tailWord_5605039 prefixEnd_5605039 2878079094196200992835401 := by
  unfold tailWord_5605039
  simp only [CollatzResearch.WordTrace]
  refine ⟨204432567140908442294594171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136288378093938961529729447 204432567140908442294594171)
  ·
    refine ⟨306648850711362663441891257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204432567140908442294594171 306648850711362663441891257)
    ·
      refine ⟨229986638033521997581418443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306648850711362663441891257 229986638033521997581418443)
      ·
        refine ⟨344979957050282996372127665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229986638033521997581418443 344979957050282996372127665)
        ·
          refine ⟨258734967787712247279095749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344979957050282996372127665 258734967787712247279095749)
          ·
            refine ⟨48512806460196046364830453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 258734967787712247279095749 48512806460196046364830453)
            ·
              refine ⟨4548075605643379346702855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48512806460196046364830453 4548075605643379346702855)
              ·
                refine ⟨6822113408465069020054283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4548075605643379346702855 6822113408465069020054283)
                ·
                  refine ⟨10233170112697603530081425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6822113408465069020054283 10233170112697603530081425)
                  ·
                    refine ⟨7674877584523202647561069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10233170112697603530081425 7674877584523202647561069)
                    ·
                      refine ⟨2878079094196200992835401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7674877584523202647561069 2878079094196200992835401)
                      ·
                        rfl

theorem cell23_5605039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 1, 2, 3].length) (baseStart_5605039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605039 prefixEnd_5605039 := by exact prefixLift 5605039
  have htrace : WordTrace (prefixWord ++ tailWord_5605039) baseStart_5605039 baseEnd_5605039 := by
    simpa [prefixWord, tailWord_5605039, baseEnd_5605039] using wordTrace_append hprefix tailTrace_5605039
  have hstable : (prefixWord ++ tailWord_5605039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605039).length < 2 ^ (prefixWord ++ tailWord_5605039).sum := by decide
  have hdescent : baseEnd_5605039 < baseStart_5605039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605046 : List Nat := [5, 1, 3, 1, 1, 1, 1, 4, 2, 4]
def baseStart_5605046 : Nat := 118140960795 + 5605046 * 2 ^ 59
def prefixEnd_5605046 : Nat := 4983230072969 + 3 ^ 40 * 5605046 * 2
def baseEnd_5605046 : Nat := 959360896186927488482623

theorem tailTrace_5605046 : CollatzResearch.WordTrace tailWord_5605046 prefixEnd_5605046 959360896186927488482623 := by
  unfold tailWord_5605046
  simp only [CollatzResearch.WordTrace]
  refine ⟨12777051403242692655631187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136288548301255388326732661 12777051403242692655631187)
  ·
    refine ⟨19165577104864038983446781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12777051403242692655631187 19165577104864038983446781)
    ·
      refine ⟨7187091414324014618792543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19165577104864038983446781 7187091414324014618792543)
      ·
        refine ⟨10780637121486021928188815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7187091414324014618792543 10780637121486021928188815)
        ·
          refine ⟨16170955682229032892283223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10780637121486021928188815 16170955682229032892283223)
          ·
            refine ⟨24256433523343549338424835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16170955682229032892283223 24256433523343549338424835)
            ·
              refine ⟨36384650285015324007637253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24256433523343549338424835 36384650285015324007637253)
              ·
                refine ⟨6822121928440373251431985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36384650285015324007637253 6822121928440373251431985)
                ·
                  refine ⟨5116591446330279938573989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6822121928440373251431985 5116591446330279938573989)
                  ·
                    refine ⟨959360896186927488482623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5116591446330279938573989 959360896186927488482623)
                    ·
                      rfl

theorem cell23_5605046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_5605046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605046 prefixEnd_5605046 := by exact prefixLift 5605046
  have htrace : WordTrace (prefixWord ++ tailWord_5605046) baseStart_5605046 baseEnd_5605046 := by
    simpa [prefixWord, tailWord_5605046, baseEnd_5605046] using wordTrace_append hprefix tailTrace_5605046
  have hstable : (prefixWord ++ tailWord_5605046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605046).length < 2 ^ (prefixWord ++ tailWord_5605046).sum := by decide
  have hdescent : baseEnd_5605046 < baseStart_5605046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605079 : List Nat := [1, 1, 3, 2, 1, 3, 2, 4, 1, 3, 2]
def baseStart_5605079 : Nat := 118140960795 + 5605079 * 2 ^ 59
def prefixEnd_5605079 : Nat := 4983230072969 + 3 ^ 40 * 5605079 * 2
def baseEnd_5605079 : Nat := 2878099633422380836335217

theorem tailTrace_5605079 : CollatzResearch.WordTrace tailWord_5605079 prefixEnd_5605079 2878099633422380836335217 := by
  unfold tailWord_5605079
  simp only [CollatzResearch.WordTrace]
  refine ⟨204434026060763529126050291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136289350707175686084033527 204434026060763529126050291)
  ·
    refine ⟨306651039091145293689075437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204434026060763529126050291 306651039091145293689075437)
    ·
      refine ⟨114994139659179485133403289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306651039091145293689075437 114994139659179485133403289)
      ·
        refine ⟨86245604744384613850052467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114994139659179485133403289 86245604744384613850052467)
        ·
          refine ⟨129368407116576920775078701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86245604744384613850052467 129368407116576920775078701)
          ·
            refine ⟨48513152668716345290654513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129368407116576920775078701 48513152668716345290654513)
            ·
              refine ⟨36384864501537258967990885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48513152668716345290654513 36384864501537258967990885)
              ·
                refine ⟨6822162094038236056498291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36384864501537258967990885 6822162094038236056498291)
                ·
                  refine ⟨10233243141057354084747437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6822162094038236056498291 10233243141057354084747437)
                  ·
                    refine ⟨3837466177896507781780289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10233243141057354084747437 3837466177896507781780289)
                    ·
                      refine ⟨2878099633422380836335217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3837466177896507781780289 2878099633422380836335217)
                      ·
                        rfl

theorem cell23_5605079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 3, 2].length) (baseStart_5605079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605079 prefixEnd_5605079 := by exact prefixLift 5605079
  have htrace : WordTrace (prefixWord ++ tailWord_5605079) baseStart_5605079 baseEnd_5605079 := by
    simpa [prefixWord, tailWord_5605079, baseEnd_5605079] using wordTrace_append hprefix tailTrace_5605079
  have hstable : (prefixWord ++ tailWord_5605079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605079).length < 2 ^ (prefixWord ++ tailWord_5605079).sum := by decide
  have hdescent : baseEnd_5605079 < baseStart_5605079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605096 : List Nat := [2, 1, 4, 1, 3, 2, 1, 3, 1, 3, 2]
def baseStart_5605096 : Nat := 118140960795 + 5605096 * 2 ^ 59
def prefixEnd_5605096 : Nat := 4983230072969 + 3 ^ 40 * 5605096 * 2
def baseEnd_5605096 : Nat := 2878108362593507269822639

theorem tailTrace_5605096 : CollatzResearch.WordTrace tailWord_5605096 prefixEnd_5605096 2878108362593507269822639 := by
  unfold tailWord_5605096
  simp only [CollatzResearch.WordTrace]
  refine ⟨102217323050850970514709571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136289764067801294019612761 102217323050850970514709571)
  ·
    refine ⟨153325984576276455772064357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102217323050850970514709571 153325984576276455772064357)
    ·
      refine ⟨28748622108051835457262067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153325984576276455772064357 28748622108051835457262067)
      ·
        refine ⟨43122933162077753185893101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28748622108051835457262067 43122933162077753185893101)
        ·
          refine ⟨16171099935779157444709913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43122933162077753185893101 16171099935779157444709913)
          ·
            refine ⟨12128324951834368083532435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16171099935779157444709913 12128324951834368083532435)
            ·
              refine ⟨18192487427751552125298653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12128324951834368083532435 18192487427751552125298653)
              ·
                refine ⟨6822182785406832046986995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18192487427751552125298653 6822182785406832046986995)
                ·
                  refine ⟨10233274178110248070480493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6822182785406832046986995 10233274178110248070480493)
                  ·
                    refine ⟨3837477816791343026430185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10233274178110248070480493 3837477816791343026430185)
                    ·
                      refine ⟨2878108362593507269822639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3837477816791343026430185 2878108362593507269822639)
                      ·
                        rfl

theorem cell23_5605096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_5605096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605096 prefixEnd_5605096 := by exact prefixLift 5605096
  have htrace : WordTrace (prefixWord ++ tailWord_5605096) baseStart_5605096 baseEnd_5605096 := by
    simpa [prefixWord, tailWord_5605096, baseEnd_5605096] using wordTrace_append hprefix tailTrace_5605096
  have hstable : (prefixWord ++ tailWord_5605096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605096).length < 2 ^ (prefixWord ++ tailWord_5605096).sum := by decide
  have hdescent : baseEnd_5605096 < baseStart_5605096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605166 : List Nat := [4, 1, 3, 2, 2, 2, 1, 1, 7]
def baseStart_5605166 : Nat := 118140960795 + 5605166 * 2 ^ 59
def prefixEnd_5605166 : Nat := 4983230072969 + 3 ^ 40 * 5605166 * 2
def baseEnd_5605166 : Nat := 319793811804369110660813

theorem tailTrace_5605166 : CollatzResearch.WordTrace tailWord_5605166 prefixEnd_5605166 319793811804369110660813 := by
  unfold tailWord_5605166
  simp only [CollatzResearch.WordTrace]
  refine ⟨25554649901431042873058419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136291466140965561989644901 25554649901431042873058419)
  ·
    refine ⟨38331974852146564309587629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25554649901431042873058419 38331974852146564309587629)
    ·
      refine ⟨14374490569554961616095361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38331974852146564309587629 14374490569554961616095361)
      ·
        refine ⟨10780867927166221212071521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14374490569554961616095361 10780867927166221212071521)
        ·
          refine ⟨8085650945374665909053641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10780867927166221212071521 8085650945374665909053641)
          ·
            refine ⟨6064238209030999431790231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8085650945374665909053641 6064238209030999431790231)
            ·
              refine ⟨9096357313546499147685347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6064238209030999431790231 9096357313546499147685347)
              ·
                refine ⟨13644535970319748721528021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9096357313546499147685347 13644535970319748721528021)
                ·
                  refine ⟨319793811804369110660813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13644535970319748721528021 319793811804369110660813)
                  ·
                    rfl

theorem cell23_5605166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 7].length) (baseStart_5605166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605166 prefixEnd_5605166 := by exact prefixLift 5605166
  have htrace : WordTrace (prefixWord ++ tailWord_5605166) baseStart_5605166 baseEnd_5605166 := by
    simpa [prefixWord, tailWord_5605166, baseEnd_5605166] using wordTrace_append hprefix tailTrace_5605166
  have hstable : (prefixWord ++ tailWord_5605166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605166).length < 2 ^ (prefixWord ++ tailWord_5605166).sum := by decide
  have hdescent : baseEnd_5605166 < baseStart_5605166 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605175 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 2, 8]
def baseStart_5605175 : Nat := 118140960795 + 5605175 * 2 ^ 59
def prefixEnd_5605175 : Nat := 4983230072969 + 3 ^ 40 * 5605175 * 2
def baseEnd_5605175 : Nat := 959382975855070820244925

theorem tailTrace_5605175 : CollatzResearch.WordTrace tailWord_5605175 prefixEnd_5605175 959382975855070820244925 := by
  unfold tailWord_5605175
  simp only [CollatzResearch.WordTrace]
  refine ⟨204437527468415737521544979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136291684978943825014363319 204437527468415737521544979)
  ·
    refine ⟨306656291202623606282317469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204437527468415737521544979 306656291202623606282317469)
    ·
      refine ⟨114996109200983852355869051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306656291202623606282317469 114996109200983852355869051)
      ·
        refine ⟨172494163801475778533803577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114996109200983852355869051 172494163801475778533803577)
        ·
          refine ⟨129370622851106833900352683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172494163801475778533803577 129370622851106833900352683)
          ·
            refine ⟨194055934276660250850529025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129370622851106833900352683 194055934276660250850529025)
            ·
              refine ⟨145541950707495188137896769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194055934276660250850529025 145541950707495188137896769)
              ·
                refine ⟨109156463030621391103422577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145541950707495188137896769 109156463030621391103422577)
                ·
                  refine ⟨81867347272966043327566933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109156463030621391103422577 81867347272966043327566933)
                  ·
                    refine ⟨959382975855070820244925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81867347272966043327566933 959382975855070820244925)
                    ·
                      rfl

theorem cell23_5605175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 8].length) (baseStart_5605175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605175 prefixEnd_5605175 := by exact prefixLift 5605175
  have htrace : WordTrace (prefixWord ++ tailWord_5605175) baseStart_5605175 baseEnd_5605175 := by
    simpa [prefixWord, tailWord_5605175, baseEnd_5605175] using wordTrace_append hprefix tailTrace_5605175
  have hstable : (prefixWord ++ tailWord_5605175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605175).length < 2 ^ (prefixWord ++ tailWord_5605175).sum := by decide
  have hdescent : baseEnd_5605175 < baseStart_5605175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605177 : List Nat := [1, 2, 1, 7, 1, 2, 2, 1, 2, 2, 2]
def baseStart_5605177 : Nat := 118140960795 + 5605177 * 2 ^ 59
def prefixEnd_5605177 : Nat := 4983230072969 + 3 ^ 40 * 5605177 * 2
def baseEnd_5605177 : Nat := 2878149954526521452909767

theorem tailTrace_5605177 : CollatzResearch.WordTrace tailWord_5605177 prefixEnd_5605177 2878149954526521452909767 := by
  unfold tailWord_5605177
  simp only [CollatzResearch.WordTrace]
  refine ⟨204437600414408491863117785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136291733609605661242078523 204437600414408491863117785)
  ·
    refine ⟨153328200310806368897338339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204437600414408491863117785 153328200310806368897338339)
    ·
      refine ⟨229992300466209553346007509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153328200310806368897338339 229992300466209553346007509)
      ·
        refine ⟨5390444542176786406547051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 229992300466209553346007509 5390444542176786406547051)
        ·
          refine ⟨8085666813265179609820577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5390444542176786406547051 8085666813265179609820577)
          ·
            refine ⟨6064250109948884707365433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8085666813265179609820577 6064250109948884707365433)
            ·
              refine ⟨4548187582461663530524075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6064250109948884707365433 4548187582461663530524075)
              ·
                refine ⟨6822281373692495295786113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4548187582461663530524075 6822281373692495295786113)
                ·
                  refine ⟨5116711030269371471839585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6822281373692495295786113 5116711030269371471839585)
                  ·
                    refine ⟨3837533272702028603879689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5116711030269371471839585 3837533272702028603879689)
                    ·
                      refine ⟨2878149954526521452909767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3837533272702028603879689 2878149954526521452909767)
                      ·
                        rfl

theorem cell23_5605177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_5605177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605177 prefixEnd_5605177 := by exact prefixLift 5605177
  have htrace : WordTrace (prefixWord ++ tailWord_5605177) baseStart_5605177 baseEnd_5605177 := by
    simpa [prefixWord, tailWord_5605177, baseEnd_5605177] using wordTrace_append hprefix tailTrace_5605177
  have hstable : (prefixWord ++ tailWord_5605177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605177).length < 2 ^ (prefixWord ++ tailWord_5605177).sum := by decide
  have hdescent : baseEnd_5605177 < baseStart_5605177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605232 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 3]
def baseStart_5605232 : Nat := 118140960795 + 5605232 * 2 ^ 59
def prefixEnd_5605232 : Nat := 4983230072969 + 3 ^ 40 * 5605232 * 2
def baseEnd_5605232 : Nat := 2878178195962518737722013

theorem tailTrace_5605232 : CollatzResearch.WordTrace tailWord_5605232 prefixEnd_5605232 2878178195962518737722013 := by
  unfold tailWord_5605232
  simp only [CollatzResearch.WordTrace]
  refine ⟨102219803214604618128184975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136293070952806157504246633 102219803214604618128184975)
  ·
    refine ⟨153329704821906927192277463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102219803214604618128184975 153329704821906927192277463)
    ·
      refine ⟨229994557232860390788416195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153329704821906927192277463 229994557232860390788416195)
      ·
        refine ⟨344991835849290586182624293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229994557232860390788416195 344991835849290586182624293)
        ·
          refine ⟨64685969221741984909242055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 344991835849290586182624293 64685969221741984909242055)
          ·
            refine ⟨97028953832612977363863083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64685969221741984909242055 97028953832612977363863083)
            ·
              refine ⟨145543430748919466045794625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97028953832612977363863083 145543430748919466045794625)
              ·
                refine ⟨109157573061689599534345969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145543430748919466045794625 109157573061689599534345969)
                ·
                  refine ⟨81868179796267199650759477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109157573061689599534345969 81868179796267199650759477)
                  ·
                    refine ⟨7675141855900049967258701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81868179796267199650759477 7675141855900049967258701)
                    ·
                      refine ⟨2878178195962518737722013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7675141855900049967258701 2878178195962518737722013)
                      ·
                        rfl

theorem cell23_5605232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 3].length) (baseStart_5605232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605232 prefixEnd_5605232 := by exact prefixLift 5605232
  have htrace : WordTrace (prefixWord ++ tailWord_5605232) baseStart_5605232 baseEnd_5605232 := by
    simpa [prefixWord, tailWord_5605232, baseEnd_5605232] using wordTrace_append hprefix tailTrace_5605232
  have hstable : (prefixWord ++ tailWord_5605232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605232).length < 2 ^ (prefixWord ++ tailWord_5605232).sum := by decide
  have hdescent : baseEnd_5605232 < baseStart_5605232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605269 : List Nat := [1, 3, 2, 1, 1, 3, 3, 3, 1, 5]
def baseStart_5605269 : Nat := 118140960795 + 5605269 * 2 ^ 59
def prefixEnd_5605269 : Nat := 4983230072969 + 3 ^ 40 * 5605269 * 2
def baseEnd_5605269 : Nat := 959399064915578364319781

theorem tailTrace_5605269 : CollatzResearch.WordTrace tailWord_5605269 prefixEnd_5605269 959399064915578364319781 := by
  unfold tailWord_5605269
  simp only [CollatzResearch.WordTrace]
  refine ⟨204440955930075191575466861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136293970620050127716977907 204440955930075191575466861)
  ·
    refine ⟨76665358473778196840800073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204440955930075191575466861 76665358473778196840800073)
    ·
      refine ⟨57499018855333647630600055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76665358473778196840800073 57499018855333647630600055)
      ·
        refine ⟨86248528283000471445900083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57499018855333647630600055 86248528283000471445900083)
        ·
          refine ⟨129372792424500707168850125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86248528283000471445900083 129372792424500707168850125)
          ·
            refine ⟨48514797159187765188318797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129372792424500707168850125 48514797159187765188318797)
            ·
              refine ⟨18193048934695411945619549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48514797159187765188318797 18193048934695411945619549)
              ·
                refine ⟨6822393350510779479607331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18193048934695411945619549 6822393350510779479607331)
                ·
                  refine ⟨10233590025766169219410997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6822393350510779479607331 10233590025766169219410997)
                  ·
                    refine ⟨959399064915578364319781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10233590025766169219410997 959399064915578364319781)
                    ·
                      rfl

theorem cell23_5605269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_5605269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605269 prefixEnd_5605269 := by exact prefixLift 5605269
  have htrace : WordTrace (prefixWord ++ tailWord_5605269) baseStart_5605269 baseEnd_5605269 := by
    simpa [prefixWord, tailWord_5605269, baseEnd_5605269] using wordTrace_append hprefix tailTrace_5605269
  have hstable : (prefixWord ++ tailWord_5605269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605269).length < 2 ^ (prefixWord ++ tailWord_5605269).sum := by decide
  have hdescent : baseEnd_5605269 < baseStart_5605269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605306 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 5, 2, 2]
def baseStart_5605306 : Nat := 118140960795 + 5605306 * 2 ^ 59
def prefixEnd_5605306 : Nat := 4983230072969 + 3 ^ 40 * 5605306 * 2
def baseEnd_5605306 : Nat := 2878216193530951448196673

theorem tailTrace_5605306 : CollatzResearch.WordTrace tailWord_5605306 prefixEnd_5605306 2878216193530951448196673 := by
  unfold tailWord_5605306
  simp only [CollatzResearch.WordTrace]
  refine ⟨51110576357735286723640943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136294870287294097929709181 51110576357735286723640943)
  ·
    refine ⟨76665864536602930085461415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51110576357735286723640943 76665864536602930085461415)
    ·
      refine ⟨114998796804904395128192123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76665864536602930085461415 114998796804904395128192123)
      ·
        refine ⟨172498195207356592692288185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114998796804904395128192123 172498195207356592692288185)
        ·
          refine ⟨129373646405517444519216139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172498195207356592692288185 129373646405517444519216139)
          ·
            refine ⟨194060469608276166778824209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129373646405517444519216139 194060469608276166778824209)
            ·
              refine ⟨145545352206207125084118157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194060469608276166778824209 145545352206207125084118157)
              ·
                refine ⟨54579507077327671906544309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145545352206207125084118157 54579507077327671906544309)
                ·
                  refine ⟨5116828788499469241238529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54579507077327671906544309 5116828788499469241238529)
                  ·
                    refine ⟨3837621591374601930928897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5116828788499469241238529 3837621591374601930928897)
                    ·
                      refine ⟨2878216193530951448196673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3837621591374601930928897 2878216193530951448196673)
                      ·
                        rfl

theorem cell23_5605306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 5, 2, 2].length) (baseStart_5605306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605306 prefixEnd_5605306 := by exact prefixLift 5605306
  have htrace : WordTrace (prefixWord ++ tailWord_5605306) baseStart_5605306 baseEnd_5605306 := by
    simpa [prefixWord, tailWord_5605306, baseEnd_5605306] using wordTrace_append hprefix tailTrace_5605306
  have hstable : (prefixWord ++ tailWord_5605306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605306).length < 2 ^ (prefixWord ++ tailWord_5605306).sum := by decide
  have hdescent : baseEnd_5605306 < baseStart_5605306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605312 : List Nat := [2, 1, 1, 2, 3, 2, 3, 9]
def baseStart_5605312 : Nat := 118140960795 + 5605312 * 2 ^ 59
def prefixEnd_5605312 : Nat := 4983230072969 + 3 ^ 40 * 5605312 * 2
def baseEnd_5605312 : Nat := 106600713867217719434135

theorem tailTrace_5605312 : CollatzResearch.WordTrace tailWord_5605312 prefixEnd_5605312 106600713867217719434135 := by
  unfold tailWord_5605312
  simp only [CollatzResearch.WordTrace]
  refine ⟨102221262134459704959641095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136295016179279606612854793 102221262134459704959641095)
  ·
    refine ⟨153331893201689557439461643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102221262134459704959641095 153331893201689557439461643)
    ·
      refine ⟨229997839802534336159192465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153331893201689557439461643 229997839802534336159192465)
      ·
        refine ⟨172498379851900752119394349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229997839802534336159192465 172498379851900752119394349)
        ·
          refine ⟨64686892444462782044772881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172498379851900752119394349 64686892444462782044772881)
          ·
            refine ⟨48515169333347086533579661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64686892444462782044772881 48515169333347086533579661)
            ·
              refine ⟨18193188500005157450092373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48515169333347086533579661 18193188500005157450092373)
              ·
                refine ⟨106600713867217719434135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18193188500005157450092373 106600713867217719434135)
                ·
                  rfl

theorem cell23_5605312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 9].length) (baseStart_5605312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605312 prefixEnd_5605312 := by exact prefixLift 5605312
  have htrace : WordTrace (prefixWord ++ tailWord_5605312) baseStart_5605312 baseEnd_5605312 := by
    simpa [prefixWord, tailWord_5605312, baseEnd_5605312] using wordTrace_append hprefix tailTrace_5605312
  have hstable : (prefixWord ++ tailWord_5605312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605312).length < 2 ^ (prefixWord ++ tailWord_5605312).sum := by decide
  have hdescent : baseEnd_5605312 < baseStart_5605312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605326 : List Nat := [4, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3]
def baseStart_5605326 : Nat := 118140960795 + 5605326 * 2 ^ 59
def prefixEnd_5605326 : Nat := 4983230072969 + 3 ^ 40 * 5605326 * 2
def baseEnd_5605326 : Nat := 2878226463144041369946581

theorem tailTrace_5605326 : CollatzResearch.WordTrace tailWord_5605326 prefixEnd_5605326 2878226463144041369946581 := by
  unfold tailWord_5605326
  simp only [CollatzResearch.WordTrace]
  refine ⟨25555379361358586288786479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136295356593912460206861221 25555379361358586288786479)
  ·
    refine ⟨38333069042037879433179719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25555379361358586288786479 38333069042037879433179719)
    ·
      refine ⟨57499603563056819149769579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38333069042037879433179719 57499603563056819149769579)
      ·
        refine ⟨86249405344585228724654369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57499603563056819149769579 86249405344585228724654369)
        ·
          refine ⟨64687054008438921543490777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86249405344585228724654369 64687054008438921543490777)
          ·
            refine ⟨48515290506329191157618083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64687054008438921543490777 48515290506329191157618083)
            ·
              refine ⟨72772935759493786736427125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48515290506329191157618083 72772935759493786736427125)
              ·
                refine ⟨6822462727452542506540043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72772935759493786736427125 6822462727452542506540043)
                ·
                  refine ⟨10233694091178813759810065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6822462727452542506540043 10233694091178813759810065)
                  ·
                    refine ⟨7675270568384110319857549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10233694091178813759810065 7675270568384110319857549)
                    ·
                      refine ⟨2878226463144041369946581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7675270568384110319857549 2878226463144041369946581)
                      ·
                        rfl

theorem cell23_5605326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_5605326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605326 prefixEnd_5605326 := by exact prefixLift 5605326
  have htrace : WordTrace (prefixWord ++ tailWord_5605326) baseStart_5605326 baseEnd_5605326 := by
    simpa [prefixWord, tailWord_5605326, baseEnd_5605326] using wordTrace_append hprefix tailTrace_5605326
  have hstable : (prefixWord ++ tailWord_5605326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605326).length < 2 ^ (prefixWord ++ tailWord_5605326).sum := by decide
  have hdescent : baseEnd_5605326 < baseStart_5605326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605334 : List Nat := [5, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3]
def baseStart_5605334 : Nat := 118140960795 + 5605334 * 2 ^ 59
def prefixEnd_5605334 : Nat := 4983230072969 + 3 ^ 40 * 5605334 * 2
def baseEnd_5605334 : Nat := 2878230570989277338646545

theorem tailTrace_5605334 : CollatzResearch.WordTrace tailWord_5605334 prefixEnd_5605334 2878230570989277338646545 := by
  unfold tailWord_5605334
  simp only [CollatzResearch.WordTrace]
  refine ⟨12777707917177481729786441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136295551116559805117722037 12777707917177481729786441)
  ·
    refine ⟨9583280937883111297339831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12777707917177481729786441 9583280937883111297339831)
    ·
      refine ⟨14374921406824666946009747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9583280937883111297339831 14374921406824666946009747)
      ·
        refine ⟨21562382110237000419014621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14374921406824666946009747 21562382110237000419014621)
        ·
          refine ⟨8085893291338875157130483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21562382110237000419014621 8085893291338875157130483)
          ·
            refine ⟨12128839937008312735695725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8085893291338875157130483 12128839937008312735695725)
            ·
              refine ⟨4548314976378117275885897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12128839937008312735695725 4548314976378117275885897)
              ·
                refine ⟨3411236232283587956914423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4548314976378117275885897 3411236232283587956914423)
                ·
                  refine ⟨5116854348425381935371635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3411236232283587956914423 5116854348425381935371635)
                  ·
                    refine ⟨7675281522638072903057453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5116854348425381935371635 7675281522638072903057453)
                    ·
                      refine ⟨2878230570989277338646545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7675281522638072903057453 2878230570989277338646545)
                      ·
                        rfl

theorem cell23_5605334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_5605334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605334 prefixEnd_5605334 := by exact prefixLift 5605334
  have htrace : WordTrace (prefixWord ++ tailWord_5605334) baseStart_5605334 baseEnd_5605334 := by
    simpa [prefixWord, tailWord_5605334, baseEnd_5605334] using wordTrace_append hprefix tailTrace_5605334
  have hstable : (prefixWord ++ tailWord_5605334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605334).length < 2 ^ (prefixWord ++ tailWord_5605334).sum := by decide
  have hdescent : baseEnd_5605334 < baseStart_5605334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605357 : List Nat := [1, 5, 1, 4, 2, 1, 1, 2, 1, 1, 4]
def baseStart_5605357 : Nat := 118140960795 + 5605357 * 2 ^ 59
def prefixEnd_5605357 : Nat := 4983230072969 + 3 ^ 40 * 5605357 * 2
def baseEnd_5605357 : Nat := 2878242381044330748658939

theorem tailTrace_5605357 : CollatzResearch.WordTrace tailWord_5605357 prefixEnd_5605357 2878242381044330748658939 := by
  unfold tailWord_5605357
  simp only [CollatzResearch.WordTrace]
  refine ⟨204444165553756382604670325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136296110369170921736446883 204444165553756382604670325)
  ·
    refine ⟨19166640520664660869187843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 204444165553756382604670325 19166640520664660869187843)
    ·
      refine ⟨28749960780996991303781765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19166640520664660869187843 28749960780996991303781765)
      ·
        refine ⟨5390617646436935869459081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28749960780996991303781765 5390617646436935869459081)
        ·
          refine ⟨4042963234827701902094311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5390617646436935869459081 4042963234827701902094311)
          ·
            refine ⟨6064444852241552853141467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4042963234827701902094311 6064444852241552853141467)
            ·
              refine ⟨9096667278362329279712201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6064444852241552853141467 9096667278362329279712201)
              ·
                refine ⟨6822500458771746959784151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9096667278362329279712201 6822500458771746959784151)
                ·
                  refine ⟨10233750688157620439676227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6822500458771746959784151 10233750688157620439676227)
                  ·
                    refine ⟨15350626032236430659514341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10233750688157620439676227 15350626032236430659514341)
                    ·
                      refine ⟨2878242381044330748658939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15350626032236430659514341 2878242381044330748658939)
                      ·
                        rfl

theorem cell23_5605357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_5605357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605357 prefixEnd_5605357 := by exact prefixLift 5605357
  have htrace : WordTrace (prefixWord ++ tailWord_5605357) baseStart_5605357 baseEnd_5605357 := by
    simpa [prefixWord, tailWord_5605357, baseEnd_5605357] using wordTrace_append hprefix tailTrace_5605357
  have hstable : (prefixWord ++ tailWord_5605357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605357).length < 2 ^ (prefixWord ++ tailWord_5605357).sum := by decide
  have hdescent : baseEnd_5605357 < baseStart_5605357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605413 : List Nat := [1, 3, 1, 2, 2, 4, 2, 1, 1, 4, 2]
def baseStart_5605413 : Nat := 118140960795 + 5605413 * 2 ^ 59
def prefixEnd_5605413 : Nat := 4983230072969 + 3 ^ 40 * 5605413 * 2
def baseEnd_5605413 : Nat := 2878271135960982529558681

theorem tailTrace_5605413 : CollatzResearch.WordTrace tailWord_5605413 prefixEnd_5605413 2878271135960982529558681 := by
  unfold tailWord_5605413
  simp only [CollatzResearch.WordTrace]
  refine ⟨204446208041553504168708893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136297472027702336112472595 204446208041553504168708893)
  ·
    refine ⟨76667328015582564063265835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204446208041553504168708893 76667328015582564063265835)
    ·
      refine ⟨115000992023373846094898753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76667328015582564063265835 115000992023373846094898753)
      ·
        refine ⟨86250744017530384571174065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115000992023373846094898753 86250744017530384571174065)
        ·
          refine ⟨64688058013147788428380549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86250744017530384571174065 64688058013147788428380549)
          ·
            refine ⟨12129010877465210330321353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64688058013147788428380549 12129010877465210330321353)
            ·
              refine ⟨9096758158098907747741015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12129010877465210330321353 9096758158098907747741015)
              ·
                refine ⟨13645137237148361621611523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9096758158098907747741015 13645137237148361621611523)
                ·
                  refine ⟨20467705855722542432417285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13645137237148361621611523 20467705855722542432417285)
                  ·
                    refine ⟨3837694847947976706078241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20467705855722542432417285 3837694847947976706078241)
                    ·
                      refine ⟨2878271135960982529558681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3837694847947976706078241 2878271135960982529558681)
                      ·
                        rfl

theorem cell23_5605413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 4, 2].length) (baseStart_5605413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605413 prefixEnd_5605413 := by exact prefixLift 5605413
  have htrace : WordTrace (prefixWord ++ tailWord_5605413) baseStart_5605413 baseEnd_5605413 := by
    simpa [prefixWord, tailWord_5605413, baseEnd_5605413] using wordTrace_append hprefix tailTrace_5605413
  have hstable : (prefixWord ++ tailWord_5605413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605413).length < 2 ^ (prefixWord ++ tailWord_5605413).sum := by decide
  have hdescent : baseEnd_5605413 < baseStart_5605413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605430 : List Nat := [5, 1, 2, 1, 1, 1, 2, 2, 4, 2, 2]
def baseStart_5605430 : Nat := 118140960795 + 5605430 * 2 ^ 59
def prefixEnd_5605430 : Nat := 4983230072969 + 3 ^ 40 * 5605430 * 2
def baseEnd_5605430 : Nat := 2878279865132108963046103

theorem tailTrace_5605430 : CollatzResearch.WordTrace tailWord_5605430 prefixEnd_5605430 2878279865132108963046103 := by
  unfold tailWord_5605430
  simp only [CollatzResearch.WordTrace]
  refine ⟨12777926755155744754504859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136297885388327944048051829 12777926755155744754504859)
  ·
    refine ⟨19166890132733617131757289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12777926755155744754504859 19166890132733617131757289)
    ·
      refine ⟨14375167599550212848817967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19166890132733617131757289 14375167599550212848817967)
      ·
        refine ⟨21562751399325319273226951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14375167599550212848817967 21562751399325319273226951)
        ·
          refine ⟨32344127098987978909840427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21562751399325319273226951 32344127098987978909840427)
          ·
            refine ⟨48516190648481968364760641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32344127098987978909840427 48516190648481968364760641)
            ·
              refine ⟨36387142986361476273570481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48516190648481968364760641 36387142986361476273570481)
              ·
                refine ⟨27290357239771107205177861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36387142986361476273570481 27290357239771107205177861)
                ·
                  refine ⟨5116941982457082600970849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27290357239771107205177861 5116941982457082600970849)
                  ·
                    refine ⟨3837706486842811950728137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5116941982457082600970849 3837706486842811950728137)
                    ·
                      refine ⟨2878279865132108963046103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3837706486842811950728137 2878279865132108963046103)
                      ·
                        rfl

theorem cell23_5605430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_5605430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605430 prefixEnd_5605430 := by exact prefixLift 5605430
  have htrace : WordTrace (prefixWord ++ tailWord_5605430) baseStart_5605430 baseEnd_5605430 := by
    simpa [prefixWord, tailWord_5605430, baseEnd_5605430] using wordTrace_append hprefix tailTrace_5605430
  have hstable : (prefixWord ++ tailWord_5605430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605430).length < 2 ^ (prefixWord ++ tailWord_5605430).sum := by decide
  have hdescent : baseEnd_5605430 < baseStart_5605430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605449 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 4, 5]
def baseStart_5605449 : Nat := 118140960795 + 5605449 * 2 ^ 59
def prefixEnd_5605449 : Nat := 4983230072969 + 3 ^ 40 * 5605449 * 2
def baseEnd_5605449 : Nat := 959429873754848129569505

theorem tailTrace_5605449 : CollatzResearch.WordTrace tailWord_5605449 prefixEnd_5605449 959429873754848129569505 := by
  unfold tailWord_5605449
  simp only [CollatzResearch.WordTrace]
  refine ⟨204447521069423082317019401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136298347379615388211346267 204447521069423082317019401)
  ·
    refine ⟨153335640802067311737764551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204447521069423082317019401 153335640802067311737764551)
    ·
      refine ⟨230003461203100967606646827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153335640802067311737764551 230003461203100967606646827)
      ·
        refine ⟨345005191804651451409970241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230003461203100967606646827 345005191804651451409970241)
        ·
          refine ⟨258753893853488588557477681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 345005191804651451409970241 258753893853488588557477681)
          ·
            refine ⟨194065420390116441418108261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258753893853488588557477681 194065420390116441418108261)
            ·
              refine ⟨36387266323146832765895299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 194065420390116441418108261 36387266323146832765895299)
              ·
                refine ⟨54580899484720249148842949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36387266323146832765895299 54580899484720249148842949)
                ·
                  refine ⟨10233918653385046715408053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54580899484720249148842949 10233918653385046715408053)
                  ·
                    refine ⟨959429873754848129569505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10233918653385046715408053 959429873754848129569505)
                    ·
                      rfl

theorem cell23_5605449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 5].length) (baseStart_5605449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605449 prefixEnd_5605449 := by exact prefixLift 5605449
  have htrace : WordTrace (prefixWord ++ tailWord_5605449) baseStart_5605449 baseEnd_5605449 := by
    simpa [prefixWord, tailWord_5605449, baseEnd_5605449] using wordTrace_append hprefix tailTrace_5605449
  have hstable : (prefixWord ++ tailWord_5605449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605449).length < 2 ^ (prefixWord ++ tailWord_5605449).sum := by decide
  have hdescent : baseEnd_5605449 < baseStart_5605449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605453 : List Nat := [1, 6, 1, 1, 1, 1, 1, 6, 5]
def baseStart_5605453 : Nat := 118140960795 + 5605453 * 2 ^ 59
def prefixEnd_5605453 : Nat := 4983230072969 + 3 ^ 40 * 5605453 * 2
def baseEnd_5605453 : Nat := 319810186131906930339833

theorem tailTrace_5605453 : CollatzResearch.WordTrace tailWord_5605453 prefixEnd_5605453 319810186131906930339833 := by
  unfold tailWord_5605453
  simp only [CollatzResearch.WordTrace]
  refine ⟨204447666961408591000165013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136298444640939060666776675 204447666961408591000165013)
  ·
    refine ⟨9583484388816027703132735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 204447666961408591000165013 9583484388816027703132735)
    ·
      refine ⟨14375226583224041554699103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9583484388816027703132735 14375226583224041554699103)
      ·
        refine ⟨21562839874836062332048655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14375226583224041554699103 21562839874836062332048655)
        ·
          refine ⟨32344259812254093498072983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21562839874836062332048655 32344259812254093498072983)
          ·
            refine ⟨48516389718381140247109475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32344259812254093498072983 48516389718381140247109475)
            ·
              refine ⟨72774584577571710370664213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48516389718381140247109475 72774584577571710370664213)
              ·
                refine ⟨3411308652073673923624885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72774584577571710370664213 3411308652073673923624885)
                ·
                  refine ⟨319810186131906930339833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3411308652073673923624885 319810186131906930339833)
                  ·
                    rfl

theorem cell23_5605453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_5605453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605453 prefixEnd_5605453 := by exact prefixLift 5605453
  have htrace : WordTrace (prefixWord ++ tailWord_5605453) baseStart_5605453 baseEnd_5605453 := by
    simpa [prefixWord, tailWord_5605453, baseEnd_5605453] using wordTrace_append hprefix tailTrace_5605453
  have hstable : (prefixWord ++ tailWord_5605453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605453).length < 2 ^ (prefixWord ++ tailWord_5605453).sum := by decide
  have hdescent : baseEnd_5605453 < baseStart_5605453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605479 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 2, 8]
def baseStart_5605479 : Nat := 118140960795 + 5605479 * 2 ^ 59
def prefixEnd_5605479 : Nat := 4983230072969 + 3 ^ 40 * 5605479 * 2
def baseEnd_5605479 : Nat := 959435008561393090444459

theorem tailTrace_5605479 : CollatzResearch.WordTrace tailWord_5605479 prefixEnd_5605479 959435008561393090444459 := by
  unfold tailWord_5605479
  simp only [CollatzResearch.WordTrace]
  refine ⟨204448615259314397440611491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136299076839542931627074327 204448615259314397440611491)
  ·
    refine ⟨306672922888971596160917237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204448615259314397440611491 306672922888971596160917237)
    ·
      refine ⟨28750586520841087140085991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 306672922888971596160917237 28750586520841087140085991)
      ·
        refine ⟨43125879781261630710128987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28750586520841087140085991 43125879781261630710128987)
        ·
          refine ⟨64688819671892446065193481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43125879781261630710128987 64688819671892446065193481)
          ·
            refine ⟨48516614753919334548895111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64688819671892446065193481 48516614753919334548895111)
            ·
              refine ⟨72774922130879001823342667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48516614753919334548895111 72774922130879001823342667)
              ·
                refine ⟨109162383196318502735014001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72774922130879001823342667 109162383196318502735014001)
                ·
                  refine ⟨81871787397238877051260501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109162383196318502735014001 81871787397238877051260501)
                  ·
                    refine ⟨959435008561393090444459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81871787397238877051260501 959435008561393090444459)
                    ·
                      rfl

theorem cell23_5605479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_5605479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605479 prefixEnd_5605479 := by exact prefixLift 5605479
  have htrace : WordTrace (prefixWord ++ tailWord_5605479) baseStart_5605479 baseEnd_5605479 := by
    simpa [prefixWord, tailWord_5605479, baseEnd_5605479] using wordTrace_append hprefix tailTrace_5605479
  have hstable : (prefixWord ++ tailWord_5605479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605479).length < 2 ^ (prefixWord ++ tailWord_5605479).sum := by decide
  have hdescent : baseEnd_5605479 < baseStart_5605479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605486 : List Nat := [4, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4]
def baseStart_5605486 : Nat := 118140960795 + 5605486 * 2 ^ 59
def prefixEnd_5605486 : Nat := 4983230072969 + 3 ^ 40 * 5605486 * 2
def baseEnd_5605486 : Nat := 2878308620048760743945845

theorem tailTrace_5605486 : CollatzResearch.WordTrace tailWord_5605486 prefixEnd_5605486 2878308620048760743945845 := by
  unfold tailWord_5605486
  simp only [CollatzResearch.WordTrace]
  refine ⟨25556108821286129704514539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136299247046859358424077541 25556108821286129704514539)
  ·
    refine ⟨38334163231929194556771809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25556108821286129704514539 38334163231929194556771809)
    ·
      refine ⟨28750622423946895917578857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38334163231929194556771809 28750622423946895917578857)
      ·
        refine ⟨21562966817960171938184143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28750622423946895917578857 21562966817960171938184143)
        ·
          refine ⟨32344450226940257907276215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21562966817960171938184143 32344450226940257907276215)
          ·
            refine ⟨48516675340410386860914323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32344450226940257907276215 48516675340410386860914323)
            ·
              refine ⟨72775013010615580291371485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48516675340410386860914323 72775013010615580291371485)
              ·
                refine ⟨27290629878980842609264307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72775013010615580291371485 27290629878980842609264307)
                ·
                  refine ⟨40935944818471263913896461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27290629878980842609264307 40935944818471263913896461)
                  ·
                    refine ⟨15350979306926723967711173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40935944818471263913896461 15350979306926723967711173)
                    ·
                      refine ⟨2878308620048760743945845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15350979306926723967711173 2878308620048760743945845)
                      ·
                        rfl

theorem cell23_5605486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_5605486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605486 prefixEnd_5605486 := by exact prefixLift 5605486
  have htrace : WordTrace (prefixWord ++ tailWord_5605486) baseStart_5605486 baseEnd_5605486 := by
    simpa [prefixWord, tailWord_5605486, baseEnd_5605486] using wordTrace_append hprefix tailTrace_5605486
  have hstable : (prefixWord ++ tailWord_5605486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605486).length < 2 ^ (prefixWord ++ tailWord_5605486).sum := by decide
  have hdescent : baseEnd_5605486 < baseStart_5605486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605529 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 1, 2, 6]
def baseStart_5605529 : Nat := 118140960795 + 5605529 * 2 ^ 59
def prefixEnd_5605529 : Nat := 4983230072969 + 3 ^ 40 * 5605529 * 2
def baseEnd_5605529 : Nat := 2878330699716904075708147

theorem tailTrace_5605529 : CollatzResearch.WordTrace tailWord_5605529 prefixEnd_5605529 2878330699716904075708147 := by
  unfold tailWord_5605529
  simp only [CollatzResearch.WordTrace]
  refine ⟨204450438909133255979931641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136300292606088837319954427 204450438909133255979931641)
  ·
    refine ⟨153337829181849941984948731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204450438909133255979931641 153337829181849941984948731)
    ·
      refine ⟨230006743772774912977423097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153337829181849941984948731 230006743772774912977423097)
      ·
        refine ⟨172505057829581184733067323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230006743772774912977423097 172505057829581184733067323)
        ·
          refine ⟨258757586744371777099600985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172505057829581184733067323 258757586744371777099600985)
          ·
            refine ⟨194068190058278832824700739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258757586744371777099600985 194068190058278832824700739)
            ·
              refine ⟨291102285087418249237051109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194068190058278832824700739 291102285087418249237051109)
              ·
                refine ⟨54581678453890921731947083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 291102285087418249237051109 54581678453890921731947083)
                ·
                  refine ⟨81872517680836382597920625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54581678453890921731947083 81872517680836382597920625)
                  ·
                    refine ⟨61404388260627286948440469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81872517680836382597920625 61404388260627286948440469)
                    ·
                      refine ⟨2878330699716904075708147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61404388260627286948440469 2878330699716904075708147)
                      ·
                        rfl

theorem cell23_5605529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_5605529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605529 prefixEnd_5605529 := by exact prefixLift 5605529
  have htrace : WordTrace (prefixWord ++ tailWord_5605529) baseStart_5605529 baseEnd_5605529 := by
    simpa [prefixWord, tailWord_5605529, baseEnd_5605529] using wordTrace_append hprefix tailTrace_5605529
  have hstable : (prefixWord ++ tailWord_5605529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605529).length < 2 ^ (prefixWord ++ tailWord_5605529).sum := by decide
  have hdescent : baseEnd_5605529 < baseStart_5605529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605540 : List Nat := [2, 3, 1, 2, 4, 1, 2, 1, 2, 2, 3]
def baseStart_5605540 : Nat := 118140960795 + 5605540 * 2 ^ 59
def prefixEnd_5605540 : Nat := 4983230072969 + 3 ^ 40 * 5605540 * 2
def baseEnd_5605540 : Nat := 2878336348004103532670597

theorem tailTrace_5605540 : CollatzResearch.WordTrace tailWord_5605540 prefixEnd_5605540 2878336348004103532670597 := by
  unfold tailWord_5605540
  simp only [CollatzResearch.WordTrace]
  refine ⟨102225420056046702429291037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136300560074728936572388049 102225420056046702429291037)
  ·
    refine ⟨38334532521017513410984139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102225420056046702429291037 38334532521017513410984139)
    ·
      refine ⟨57501798781526270116476209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38334532521017513410984139 57501798781526270116476209)
      ·
        refine ⟨43126349086144702587357157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57501798781526270116476209 43126349086144702587357157)
        ·
          refine ⟨8086190453652131735129467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43126349086144702587357157 8086190453652131735129467)
          ·
            refine ⟨12129285680478197602694201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8086190453652131735129467 12129285680478197602694201)
            ·
              refine ⟨9096964260358648202020651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12129285680478197602694201 9096964260358648202020651)
              ·
                refine ⟨13645446390537972303030977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9096964260358648202020651 13645446390537972303030977)
                ·
                  refine ⟨10234084792903479227273233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13645446390537972303030977 10234084792903479227273233)
                  ·
                    refine ⟨7675563594677609420454925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10234084792903479227273233 7675563594677609420454925)
                    ·
                      refine ⟨2878336348004103532670597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7675563594677609420454925 2878336348004103532670597)
                      ·
                        rfl

theorem cell23_5605540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_5605540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605540 prefixEnd_5605540 := by exact prefixLift 5605540
  have htrace : WordTrace (prefixWord ++ tailWord_5605540) baseStart_5605540 baseEnd_5605540 := by
    simpa [prefixWord, tailWord_5605540, baseEnd_5605540] using wordTrace_append hprefix tailTrace_5605540
  have hstable : (prefixWord ++ tailWord_5605540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605540).length < 2 ^ (prefixWord ++ tailWord_5605540).sum := by decide
  have hdescent : baseEnd_5605540 < baseStart_5605540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605563 : List Nat := [1, 1, 1, 1, 1, 2, 5, 4, 2, 3, 2]
def baseStart_5605563 : Nat := 118140960795 + 5605563 * 2 ^ 59
def prefixEnd_5605563 : Nat := 4983230072969 + 3 ^ 40 * 5605563 * 2
def baseEnd_5605563 : Nat := 2878348158059156942682991

theorem tailTrace_5605563 : CollatzResearch.WordTrace tailWord_5605563 prefixEnd_5605563 2878348158059156942682991 := by
  unfold tailWord_5605563
  simp only [CollatzResearch.WordTrace]
  refine ⟨204451678991010079786669343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136301119327340053191112895 204451678991010079786669343)
  ·
    refine ⟨306677518486515119680004015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204451678991010079786669343 306677518486515119680004015)
    ·
      refine ⟨460016277729772679520006023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306677518486515119680004015 460016277729772679520006023)
      ·
        refine ⟨690024416594659019280009035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460016277729772679520006023 690024416594659019280009035)
        ·
          refine ⟨1035036624891988528920013553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 690024416594659019280009035 1035036624891988528920013553)
          ·
            refine ⟨776277468668991396690010165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1035036624891988528920013553 776277468668991396690010165)
            ·
              refine ⟨72776012687717943439688453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 776277468668991396690010165 72776012687717943439688453)
              ·
                refine ⟨13645502378947114394941585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72776012687717943439688453 13645502378947114394941585)
                ·
                  refine ⟨10234126784210335796206189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13645502378947114394941585 10234126784210335796206189)
                  ·
                    refine ⟨3837797544078875923577321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10234126784210335796206189 3837797544078875923577321)
                    ·
                      refine ⟨2878348158059156942682991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3837797544078875923577321 2878348158059156942682991)
                      ·
                        rfl

theorem cell23_5605563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 3, 2].length) (baseStart_5605563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605563 prefixEnd_5605563 := by exact prefixLift 5605563
  have htrace : WordTrace (prefixWord ++ tailWord_5605563) baseStart_5605563 baseEnd_5605563 := by
    simpa [prefixWord, tailWord_5605563, baseEnd_5605563] using wordTrace_append hprefix tailTrace_5605563
  have hstable : (prefixWord ++ tailWord_5605563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605563).length < 2 ^ (prefixWord ++ tailWord_5605563).sum := by decide
  have hdescent : baseEnd_5605563 < baseStart_5605563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605564 : List Nat := [2, 2, 2, 3, 3, 2, 2, 2, 1, 4]
def baseStart_5605564 : Nat := 118140960795 + 5605564 * 2 ^ 59
def prefixEnd_5605564 : Nat := 4983230072969 + 3 ^ 40 * 5605564 * 2
def baseEnd_5605564 : Nat := 959449557179937146256829

theorem tailTrace_5605564 : CollatzResearch.WordTrace tailWord_5605564 prefixEnd_5605564 959449557179937146256829 := by
  unfold tailWord_5605564
  simp only [CollatzResearch.WordTrace]
  refine ⟨102225857732003228478727873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136301143642670971304970497 102225857732003228478727873)
  ·
    refine ⟨76669393299002421359045905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102225857732003228478727873 76669393299002421359045905)
    ·
      refine ⟨57502044974251816019284429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76669393299002421359045905 57502044974251816019284429)
      ·
        refine ⟨21563266865344431007231661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57502044974251816019284429 21563266865344431007231661)
        ·
          refine ⟨8086225074504161627711873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21563266865344431007231661 8086225074504161627711873)
          ·
            refine ⟨6064668805878121220783905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8086225074504161627711873 6064668805878121220783905)
            ·
              refine ⟨4548501604408590915587929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6064668805878121220783905 4548501604408590915587929)
              ·
                refine ⟨3411376203306443186690947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4548501604408590915587929 3411376203306443186690947)
                ·
                  refine ⟨5117064304959664780036421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3411376203306443186690947 5117064304959664780036421)
                  ·
                    refine ⟨959449557179937146256829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5117064304959664780036421 959449557179937146256829)
                    ·
                      rfl

theorem cell23_5605564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_5605564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605564 prefixEnd_5605564 := by exact prefixLift 5605564
  have htrace : WordTrace (prefixWord ++ tailWord_5605564) baseStart_5605564 baseEnd_5605564 := by
    simpa [prefixWord, tailWord_5605564, baseEnd_5605564] using wordTrace_append hprefix tailTrace_5605564
  have hstable : (prefixWord ++ tailWord_5605564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605564).length < 2 ^ (prefixWord ++ tailWord_5605564).sum := by decide
  have hdescent : baseEnd_5605564 < baseStart_5605564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605590 : List Nat := [5, 2, 1, 2, 1, 1, 2, 1, 3, 5]
def baseStart_5605590 : Nat := 118140960795 + 5605590 * 2 ^ 59
def prefixEnd_5605590 : Nat := 4983230072969 + 3 ^ 40 * 5605590 * 2
def baseEnd_5605590 : Nat := 959454007345609445681789

theorem tailTrace_5605590 : CollatzResearch.WordTrace tailWord_5605590 prefixEnd_5605590 959454007345609445681789 := by
  unfold tailWord_5605590
  simp only [CollatzResearch.WordTrace]
  refine ⟨12778291485119516462368889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136301775841274842265268149 12778291485119516462368889)
  ·
    refine ⟨9583718613839637346776667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12778291485119516462368889 9583718613839637346776667)
    ·
      refine ⟨14375577920759456020165001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9583718613839637346776667 14375577920759456020165001)
      ·
        refine ⟨10781683440569592015123751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14375577920759456020165001 10781683440569592015123751)
        ·
          refine ⟨16172525160854388022685627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10781683440569592015123751 16172525160854388022685627)
          ·
            refine ⟨24258787741281582034028441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16172525160854388022685627 24258787741281582034028441)
            ·
              refine ⟨18194090805961186525521331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24258787741281582034028441 18194090805961186525521331)
              ·
                refine ⟨27291136208941779788281997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18194090805961186525521331 27291136208941779788281997)
                ·
                  refine ⟨10234176078353167420605749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27291136208941779788281997 10234176078353167420605749)
                  ·
                    refine ⟨959454007345609445681789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10234176078353167420605749 959454007345609445681789)
                    ·
                      rfl

theorem cell23_5605590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_5605590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605590 prefixEnd_5605590 := by exact prefixLift 5605590
  have htrace : WordTrace (prefixWord ++ tailWord_5605590) baseStart_5605590 baseEnd_5605590 := by
    simpa [prefixWord, tailWord_5605590, baseEnd_5605590] using wordTrace_append hprefix tailTrace_5605590
  have hstable : (prefixWord ++ tailWord_5605590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605590).length < 2 ^ (prefixWord ++ tailWord_5605590).sum := by decide
  have hdescent : baseEnd_5605590 < baseStart_5605590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605597 : List Nat := [1, 4, 3, 2, 1, 1, 3, 1, 2, 3, 2]
def baseStart_5605597 : Nat := 118140960795 + 5605597 * 2 ^ 59
def prefixEnd_5605597 : Nat := 4983230072969 + 3 ^ 40 * 5605597 * 2
def baseEnd_5605597 : Nat := 2878365616401409809657835

theorem tailTrace_5605597 : CollatzResearch.WordTrace tailWord_5605597 prefixEnd_5605597 2878365616401409809657835 := by
  unfold tailWord_5605597
  simp only [CollatzResearch.WordTrace]
  refine ⟨204452919072886903593407045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136301946048591269062271363 204452919072886903593407045)
  ·
    refine ⟨38334922326166294423763821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204452919072886903593407045 38334922326166294423763821)
    ·
      refine ⟨14375595872312360408911433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38334922326166294423763821 14375595872312360408911433)
      ·
        refine ⟨10781696904234270306683575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14375595872312360408911433 10781696904234270306683575)
        ·
          refine ⟨16172545356351405460025363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10781696904234270306683575 16172545356351405460025363)
          ·
            refine ⟨24258818034527108190038045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16172545356351405460025363 24258818034527108190038045)
            ·
              refine ⟨9097056762947665571264267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24258818034527108190038045 9097056762947665571264267)
              ·
                refine ⟨13645585144421498356896401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9097056762947665571264267 13645585144421498356896401)
                ·
                  refine ⟨10234188858316123767672301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13645585144421498356896401 10234188858316123767672301)
                  ·
                    refine ⟨3837820821868546412877113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10234188858316123767672301 3837820821868546412877113)
                    ·
                      refine ⟨2878365616401409809657835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3837820821868546412877113 2878365616401409809657835)
                      ·
                        rfl

theorem cell23_5605597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_5605597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605597 prefixEnd_5605597 := by exact prefixLift 5605597
  have htrace : WordTrace (prefixWord ++ tailWord_5605597) baseStart_5605597 baseEnd_5605597 := by
    simpa [prefixWord, tailWord_5605597, baseEnd_5605597] using wordTrace_append hprefix tailTrace_5605597
  have hstable : (prefixWord ++ tailWord_5605597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605597).length < 2 ^ (prefixWord ++ tailWord_5605597).sum := by decide
  have hdescent : baseEnd_5605597 < baseStart_5605597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605607 : List Nat := [1, 1, 5, 3, 1, 3, 2, 1, 1, 5]
def baseStart_5605607 : Nat := 118140960795 + 5605607 * 2 ^ 59
def prefixEnd_5605607 : Nat := 4983230072969 + 3 ^ 40 * 5605607 * 2
def baseEnd_5605607 : Nat := 959456917069318256844263

theorem tailTrace_5605607 : CollatzResearch.WordTrace tailWord_5605607 prefixEnd_5605607 959456917069318256844263 := by
  unfold tailWord_5605607
  simp only [CollatzResearch.WordTrace]
  refine ⟨204453283802850675301271075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136302189201900450200847383 204453283802850675301271075)
  ·
    refine ⟨306679925704276012951906613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204453283802850675301271075 306679925704276012951906613)
    ·
      refine ⟨28751243034775876214241245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 306679925704276012951906613 28751243034775876214241245)
      ·
        refine ⟨10781716138040953580340467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28751243034775876214241245 10781716138040953580340467)
        ·
          refine ⟨16172574207061430370510701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10781716138040953580340467 16172574207061430370510701)
          ·
            refine ⟨6064715327648036388941513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16172574207061430370510701 6064715327648036388941513)
            ·
              refine ⟨4548536495736027291706135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6064715327648036388941513 4548536495736027291706135)
              ·
                refine ⟨6822804743604040937559203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4548536495736027291706135 6822804743604040937559203)
                ·
                  refine ⟨10234207115406061406338805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6822804743604040937559203 10234207115406061406338805)
                  ·
                    refine ⟨959456917069318256844263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10234207115406061406338805 959456917069318256844263)
                    ·
                      rfl

theorem cell23_5605607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_5605607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605607 prefixEnd_5605607 := by exact prefixLift 5605607
  have htrace : WordTrace (prefixWord ++ tailWord_5605607) baseStart_5605607 baseEnd_5605607 := by
    simpa [prefixWord, tailWord_5605607, baseEnd_5605607] using wordTrace_append hprefix tailTrace_5605607
  have hstable : (prefixWord ++ tailWord_5605607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605607).length < 2 ^ (prefixWord ++ tailWord_5605607).sum := by decide
  have hdescent : baseEnd_5605607 < baseStart_5605607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605610 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 5, 2, 2]
def baseStart_5605610 : Nat := 118140960795 + 5605610 * 2 ^ 59
def prefixEnd_5605610 : Nat := 4983230072969 + 3 ^ 40 * 5605610 * 2
def baseEnd_5605610 : Nat := 2878372291649918258795275

theorem tailTrace_5605610 : CollatzResearch.WordTrace tailWord_5605610 prefixEnd_5605610 2878372291649918258795275 := by
  unfold tailWord_5605610
  simp only [CollatzResearch.WordTrace]
  refine ⟨51113348305459951703407571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136302262147893204542420189 51113348305459951703407571)
  ·
    refine ⟨76670022458189927555111357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51113348305459951703407571 76670022458189927555111357)
    ·
      refine ⟨28751258421821222833166759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76670022458189927555111357 28751258421821222833166759)
      ·
        refine ⟨43126887632731834249750139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28751258421821222833166759 43126887632731834249750139)
        ·
          refine ⟨64690331449097751374625209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43126887632731834249750139 64690331449097751374625209)
          ·
            refine ⟨48517748586823313530968907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64690331449097751374625209 48517748586823313530968907)
            ·
              refine ⟨72776622880234970296453361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48517748586823313530968907 72776622880234970296453361)
              ·
                refine ⟨54582467160176227722340021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72776622880234970296453361 54582467160176227722340021)
                ·
                  refine ⟨5117106296266521348969377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54582467160176227722340021 5117106296266521348969377)
                  ·
                    refine ⟨3837829722199891011727033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5117106296266521348969377 3837829722199891011727033)
                    ·
                      refine ⟨2878372291649918258795275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3837829722199891011727033 2878372291649918258795275)
                      ·
                        rfl

theorem cell23_5605610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_5605610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605610 prefixEnd_5605610 := by exact prefixLift 5605610
  have htrace : WordTrace (prefixWord ++ tailWord_5605610) baseStart_5605610 baseEnd_5605610 := by
    simpa [prefixWord, tailWord_5605610, baseEnd_5605610] using wordTrace_append hprefix tailTrace_5605610
  have hstable : (prefixWord ++ tailWord_5605610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605610).length < 2 ^ (prefixWord ++ tailWord_5605610).sum := by decide
  have hdescent : baseEnd_5605610 < baseStart_5605610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605640 : List Nat := [2, 1, 3, 2, 3, 3, 1, 1, 1, 2, 4]
def baseStart_5605640 : Nat := 118140960795 + 5605640 * 2 ^ 59
def prefixEnd_5605640 : Nat := 4983230072969 + 3 ^ 40 * 5605640 * 2
def baseEnd_5605640 : Nat := 2878387696069553141420137

theorem tailTrace_5605640 : CollatzResearch.WordTrace tailWord_5605640 prefixEnd_5605640 2878387696069553141420137 := by
  unfold tailWord_5605640
  simp only [CollatzResearch.WordTrace]
  refine ⟨102227243705865560968611187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136302991607820747958148249 102227243705865560968611187)
  ·
    refine ⟨153340865558798341452916781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102227243705865560968611187 153340865558798341452916781)
    ·
      refine ⟨57502824584549378044843793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153340865558798341452916781 57502824584549378044843793)
      ·
        refine ⟨43127118438412033533632845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57502824584549378044843793 43127118438412033533632845)
        ·
          refine ⟨16172669414404512575112317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43127118438412033533632845 16172669414404512575112317)
          ·
            refine ⟨6064751030401692215667119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16172669414404512575112317 6064751030401692215667119)
            ·
              refine ⟨9097126545602538323500679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6064751030401692215667119 9097126545602538323500679)
              ·
                refine ⟨13645689818403807485251019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9097126545602538323500679 13645689818403807485251019)
                ·
                  refine ⟨20468534727605711227876529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13645689818403807485251019 20468534727605711227876529)
                  ·
                    refine ⟨15351401045704283420907397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20468534727605711227876529 15351401045704283420907397)
                    ·
                      refine ⟨2878387696069553141420137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15351401045704283420907397 2878387696069553141420137)
                      ·
                        rfl

theorem cell23_5605640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_5605640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605640 prefixEnd_5605640 := by exact prefixLift 5605640
  have htrace : WordTrace (prefixWord ++ tailWord_5605640) baseStart_5605640 baseEnd_5605640 := by
    simpa [prefixWord, tailWord_5605640, baseEnd_5605640] using wordTrace_append hprefix tailTrace_5605640
  have hstable : (prefixWord ++ tailWord_5605640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605640).length < 2 ^ (prefixWord ++ tailWord_5605640).sum := by decide
  have hdescent : baseEnd_5605640 < baseStart_5605640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605656 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 1, 4, 5]
def baseStart_5605656 : Nat := 118140960795 + 5605656 * 2 ^ 59
def prefixEnd_5605656 : Nat := 4983230072969 + 3 ^ 40 * 5605656 * 2
def baseEnd_5605656 : Nat := 2878395911760025078820063

theorem tailTrace_5605656 : CollatzResearch.WordTrace tailWord_5605656 prefixEnd_5605656 2878395911760025078820063 := by
  unfold tailWord_5605656
  simp only [CollatzResearch.WordTrace]
  refine ⟨102227535489836578334902411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136303380653115437779869881 102227535489836578334902411)
  ·
    refine ⟨153341303234754867502353617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102227535489836578334902411 153341303234754867502353617)
    ·
      refine ⟨115005977426066150626765213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153341303234754867502353617 115005977426066150626765213)
      ·
        refine ⟨43127241534774806485036955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115005977426066150626765213 43127241534774806485036955)
        ·
          refine ⟨64690862302162209727555433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43127241534774806485036955 64690862302162209727555433)
          ·
            refine ⟨48518146726621657295666575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64690862302162209727555433 48518146726621657295666575)
            ·
              refine ⟨72777220089932485943499863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48518146726621657295666575 72777220089932485943499863)
              ·
                refine ⟨109165830134898728915249795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72777220089932485943499863 109165830134898728915249795)
                ·
                  refine ⟨163748745202348093372874693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109165830134898728915249795 163748745202348093372874693)
                  ·
                    refine ⟨30702889725440267507414005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 163748745202348093372874693 30702889725440267507414005)
                    ·
                      refine ⟨2878395911760025078820063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30702889725440267507414005 2878395911760025078820063)
                      ·
                        rfl

theorem cell23_5605656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_5605656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605656 prefixEnd_5605656 := by exact prefixLift 5605656
  have htrace : WordTrace (prefixWord ++ tailWord_5605656) baseStart_5605656 baseEnd_5605656 := by
    simpa [prefixWord, tailWord_5605656, baseEnd_5605656] using wordTrace_append hprefix tailTrace_5605656
  have hstable : (prefixWord ++ tailWord_5605656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605656).length < 2 ^ (prefixWord ++ tailWord_5605656).sum := by decide
  have hdescent : baseEnd_5605656 < baseStart_5605656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605676 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 4, 6]
def baseStart_5605676 : Nat := 118140960795 + 5605676 * 2 ^ 59
def prefixEnd_5605676 : Nat := 4983230072969 + 3 ^ 40 * 5605676 * 2
def baseEnd_5605676 : Nat := 959468727124371666856657

theorem tailTrace_5605676 : CollatzResearch.WordTrace tailWord_5605676 prefixEnd_5605676 959468727124371666856657 := by
  unfold tailWord_5605676
  simp only [CollatzResearch.WordTrace]
  refine ⟨102227900219800350042766441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136303866959733800057021921 102227900219800350042766441)
  ·
    refine ⟨76670925164850262532074831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102227900219800350042766441 76670925164850262532074831)
    ·
      refine ⟨115006387747275393798112247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76670925164850262532074831 115006387747275393798112247)
      ·
        refine ⟨172509581620913090697168371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115006387747275393798112247 172509581620913090697168371)
        ·
          refine ⟨258764372431369636045752557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172509581620913090697168371 258764372431369636045752557)
          ·
            refine ⟨97036639661763613517157209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 258764372431369636045752557 97036639661763613517157209)
            ·
              refine ⟨72777479746322710137867907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97036639661763613517157209 72777479746322710137867907)
              ·
                refine ⟨109166219619484065206801861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72777479746322710137867907 109166219619484065206801861)
                ·
                  refine ⟨20468666178653262226275349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109166219619484065206801861 20468666178653262226275349)
                  ·
                    refine ⟨959468727124371666856657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20468666178653262226275349 959468727124371666856657)
                    ·
                      rfl

theorem cell23_5605676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 6].length) (baseStart_5605676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605676 prefixEnd_5605676 := by exact prefixLift 5605676
  have htrace : WordTrace (prefixWord ++ tailWord_5605676) baseStart_5605676 baseEnd_5605676 := by
    simpa [prefixWord, tailWord_5605676, baseEnd_5605676] using wordTrace_append hprefix tailTrace_5605676
  have hstable : (prefixWord ++ tailWord_5605676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605676).length < 2 ^ (prefixWord ++ tailWord_5605676).sum := by decide
  have hdescent : baseEnd_5605676 < baseStart_5605676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605678 : List Nat := [4, 1, 3, 3, 2, 1, 1, 1, 3, 2, 2]
def baseStart_5605678 : Nat := 118140960795 + 5605678 * 2 ^ 59
def prefixEnd_5605678 : Nat := 4983230072969 + 3 ^ 40 * 5605678 * 2
def baseEnd_5605678 : Nat := 2878407208334423992744963

theorem tailTrace_5605678 : CollatzResearch.WordTrace tailWord_5605678 prefixEnd_5605678 2878407208334423992744963 := by
  unfold tailWord_5605678
  simp only [CollatzResearch.WordTrace]
  refine ⟨25556984173199181803388211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136303915590395636284737125 25556984173199181803388211)
  ·
    refine ⟨38335476259798772705082317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25556984173199181803388211 38335476259798772705082317)
    ·
      refine ⟨14375803597424539764405869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38335476259798772705082317 14375803597424539764405869)
      ·
        refine ⟨5390926349034202411652201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14375803597424539764405869 5390926349034202411652201)
        ·
          refine ⟨4043194761775651808739151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5390926349034202411652201 4043194761775651808739151)
          ·
            refine ⟨6064792142663477713108727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4043194761775651808739151 6064792142663477713108727)
            ·
              refine ⟨9097188213995216569663091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6064792142663477713108727 9097188213995216569663091)
              ·
                refine ⟨13645782320992824854494637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9097188213995216569663091 13645782320992824854494637)
                ·
                  refine ⟨5117168370372309320435489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13645782320992824854494637 5117168370372309320435489)
                  ·
                    refine ⟨3837876277779231990326617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5117168370372309320435489 3837876277779231990326617)
                    ·
                      refine ⟨2878407208334423992744963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3837876277779231990326617 2878407208334423992744963)
                      ·
                        rfl

theorem cell23_5605678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_5605678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605678 prefixEnd_5605678 := by exact prefixLift 5605678
  have htrace : WordTrace (prefixWord ++ tailWord_5605678) baseStart_5605678 baseEnd_5605678 := by
    simpa [prefixWord, tailWord_5605678, baseEnd_5605678] using wordTrace_append hprefix tailTrace_5605678
  have hstable : (prefixWord ++ tailWord_5605678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605678).length < 2 ^ (prefixWord ++ tailWord_5605678).sum := by decide
  have hdescent : baseEnd_5605678 < baseStart_5605678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605694 : List Nat := [4, 2, 1, 2, 1, 2, 4, 1, 2, 1, 3]
def baseStart_5605694 : Nat := 118140960795 + 5605694 * 2 ^ 59
def prefixEnd_5605694 : Nat := 4983230072969 + 3 ^ 40 * 5605694 * 2
def baseEnd_5605694 : Nat := 2878415424024895930144889

theorem tailTrace_5605694 : CollatzResearch.WordTrace tailWord_5605694 prefixEnd_5605694 2878415424024895930144889 := by
  unfold tailWord_5605694
  simp only [CollatzResearch.WordTrace]
  refine ⟨25557057119191936144961017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136304304635690326106458757 25557057119191936144961017)
  ·
    refine ⟨19167792839393952108720763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25557057119191936144961017 19167792839393952108720763)
    ·
      refine ⟨28751689259090928163081145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19167792839393952108720763 28751689259090928163081145)
      ·
        refine ⟨21563766944318196122310859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28751689259090928163081145 21563766944318196122310859)
        ·
          refine ⟨32345650416477294183466289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21563766944318196122310859 32345650416477294183466289)
          ·
            refine ⟨24259237812357970637599717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32345650416477294183466289 24259237812357970637599717)
            ·
              refine ⟨4548607089817119494549947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24259237812357970637599717 4548607089817119494549947)
              ·
                refine ⟨6822910634725679241824921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4548607089817119494549947 6822910634725679241824921)
                ·
                  refine ⟨5117182976044259431368691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6822910634725679241824921 5117182976044259431368691)
                  ·
                    refine ⟨7675774464066389147053037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5117182976044259431368691 7675774464066389147053037)
                    ·
                      refine ⟨2878415424024895930144889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7675774464066389147053037 2878415424024895930144889)
                      ·
                        rfl

theorem cell23_5605694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_5605694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605694 prefixEnd_5605694 := by exact prefixLift 5605694
  have htrace : WordTrace (prefixWord ++ tailWord_5605694) baseStart_5605694 baseEnd_5605694 := by
    simpa [prefixWord, tailWord_5605694, baseEnd_5605694] using wordTrace_append hprefix tailTrace_5605694
  have hstable : (prefixWord ++ tailWord_5605694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605694).length < 2 ^ (prefixWord ++ tailWord_5605694).sum := by decide
  have hdescent : baseEnd_5605694 < baseStart_5605694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605717 : List Nat := [1, 3, 2, 2, 4, 1, 1, 2, 1, 4, 2]
def baseStart_5605717 : Nat := 118140960795 + 5605717 * 2 ^ 59
def prefixEnd_5605717 : Nat := 4983230072969 + 3 ^ 40 * 5605717 * 2
def baseEnd_5605717 : Nat := 2878427234079949340157283

theorem tailTrace_5605717 : CollatzResearch.WordTrace tailWord_5605717 prefixEnd_5605717 2878427234079949340157283 := by
  unfold tailWord_5605717
  simp only [CollatzResearch.WordTrace]
  refine ⟨204457295832452164087775405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136304863888301442725183603 204457295832452164087775405)
  ·
    refine ⟨76671485937169561532915777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204457295832452164087775405 76671485937169561532915777)
    ·
      refine ⟨57503614452877171149686833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76671485937169561532915777 57503614452877171149686833)
      ·
        refine ⟨43127710839657878362265125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57503614452877171149686833 43127710839657878362265125)
        ·
          refine ⟨8086445782435852192924711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43127710839657878362265125 8086445782435852192924711)
          ·
            refine ⟨12129668673653778289387067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8086445782435852192924711 12129668673653778289387067)
            ·
              refine ⟨18194503010480667434080601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12129668673653778289387067 18194503010480667434080601)
              ·
                refine ⟨13645877257860500575560451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18194503010480667434080601 13645877257860500575560451)
                ·
                  refine ⟨20468815886790750863340677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13645877257860500575560451 20468815886790750863340677)
                  ·
                    refine ⟨3837902978773265786876377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20468815886790750863340677 3837902978773265786876377)
                    ·
                      refine ⟨2878427234079949340157283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3837902978773265786876377 2878427234079949340157283)
                      ·
                        rfl

theorem cell23_5605717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_5605717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605717 prefixEnd_5605717 := by exact prefixLift 5605717
  have htrace : WordTrace (prefixWord ++ tailWord_5605717) baseStart_5605717 baseEnd_5605717 := by
    simpa [prefixWord, tailWord_5605717, baseEnd_5605717] using wordTrace_append hprefix tailTrace_5605717
  have hstable : (prefixWord ++ tailWord_5605717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605717).length < 2 ^ (prefixWord ++ tailWord_5605717).sum := by decide
  have hdescent : baseEnd_5605717 < baseStart_5605717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605880 : List Nat := [2, 1, 2, 1, 1, 4, 3, 1, 3, 1, 4]
def baseStart_5605880 : Nat := 118140960795 + 5605880 * 2 ^ 59
def prefixEnd_5605880 : Nat := 4983230072969 + 3 ^ 40 * 5605880 * 2
def baseEnd_5605880 : Nat := 2878510931426632202419033

theorem tailTrace_5605880 : CollatzResearch.WordTrace tailWord_5605880 prefixEnd_5605880 2878510931426632202419033 := by
  unfold tailWord_5605880
  simp only [CollatzResearch.WordTrace]
  refine ⟨102231620465430821462979547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136308827287241095283972729 102231620465430821462979547)
  ·
    refine ⟨153347430698146232194469321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102231620465430821462979547 153347430698146232194469321)
    ·
      refine ⟨115010573023609674145851991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153347430698146232194469321 115010573023609674145851991)
      ·
        refine ⟨172515859535414511218777987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115010573023609674145851991 172515859535414511218777987)
        ·
          refine ⟨258773789303121766828166981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172515859535414511218777987 258773789303121766828166981)
          ·
            refine ⟨48520085494335331280281309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 258773789303121766828166981 48520085494335331280281309)
            ·
              refine ⟨18195032060375749230105491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48520085494335331280281309 18195032060375749230105491)
              ·
                refine ⟨27292548090563623845158237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18195032060375749230105491 27292548090563623845158237)
                ·
                  refine ⟨10234705533961358941934339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27292548090563623845158237 10234705533961358941934339)
                  ·
                    refine ⟨15352058300942038412901509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10234705533961358941934339 15352058300942038412901509)
                    ·
                      refine ⟨2878510931426632202419033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15352058300942038412901509 2878510931426632202419033)
                      ·
                        rfl

theorem cell23_5605880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_5605880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605880 prefixEnd_5605880 := by exact prefixLift 5605880
  have htrace : WordTrace (prefixWord ++ tailWord_5605880) baseStart_5605880 baseEnd_5605880 := by
    simpa [prefixWord, tailWord_5605880, baseEnd_5605880] using wordTrace_append hprefix tailTrace_5605880
  have hstable : (prefixWord ++ tailWord_5605880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605880).length < 2 ^ (prefixWord ++ tailWord_5605880).sum := by decide
  have hdescent : baseEnd_5605880 < baseStart_5605880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605897 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 7, 2, 2]
def baseStart_5605897 : Nat := 118140960795 + 5605897 * 2 ^ 59
def prefixEnd_5605897 : Nat := 4983230072969 + 3 ^ 40 * 5605897 * 2
def baseEnd_5605897 : Nat := 2878519660597758635906455

theorem tailTrace_5605897 : CollatzResearch.WordTrace tailWord_5605897 prefixEnd_5605897 2878519660597758635906455 := by
  unfold tailWord_5605897
  simp only [CollatzResearch.WordTrace]
  refine ⟨204463860971800054829327945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136309240647866703219551963 204463860971800054829327945)
  ·
    refine ⟨153347895728850041121995959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204463860971800054829327945 153347895728850041121995959)
    ·
      refine ⟨230021843593275061682993939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153347895728850041121995959 230021843593275061682993939)
      ·
        refine ⟨345032765389912592524490909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230021843593275061682993939 345032765389912592524490909)
        ·
          refine ⟨129387287021217222196684091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 345032765389912592524490909 129387287021217222196684091)
          ·
            refine ⟨194080930531825833295026137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129387287021217222196684091 194080930531825833295026137)
            ·
              refine ⟨145560697898869374971269603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194080930531825833295026137 145560697898869374971269603)
              ·
                refine ⟨218341046848304062456904405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145560697898869374971269603 218341046848304062456904405)
                ·
                  refine ⟨5117368285507126463833697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 218341046848304062456904405 5117368285507126463833697)
                  ·
                    refine ⟨3838026214130344847875273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5117368285507126463833697 3838026214130344847875273)
                    ·
                      refine ⟨2878519660597758635906455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3838026214130344847875273 2878519660597758635906455)
                      ·
                        rfl

theorem cell23_5605897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 7, 2, 2].length) (baseStart_5605897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605897 prefixEnd_5605897 := by exact prefixLift 5605897
  have htrace : WordTrace (prefixWord ++ tailWord_5605897) baseStart_5605897 baseEnd_5605897 := by
    simpa [prefixWord, tailWord_5605897, baseEnd_5605897] using wordTrace_append hprefix tailTrace_5605897
  have hstable : (prefixWord ++ tailWord_5605897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605897).length < 2 ^ (prefixWord ++ tailWord_5605897).sum := by decide
  have hdescent : baseEnd_5605897 < baseStart_5605897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605907 : List Nat := [1, 1, 1, 2, 1, 5, 4, 2, 2, 4]
def baseStart_5605907 : Nat := 118140960795 + 5605907 * 2 ^ 59
def prefixEnd_5605907 : Nat := 4983230072969 + 3 ^ 40 * 5605907 * 2
def baseEnd_5605907 : Nat := 959508265134767865593803

theorem tailTrace_5605907 : CollatzResearch.WordTrace tailWord_5605907 prefixEnd_5605907 959508265134767865593803 := by
  unfold tailWord_5605907
  simp only [CollatzResearch.WordTrace]
  refine ⟨204464225701763826537191975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136309483801175884358127983 204464225701763826537191975)
  ·
    refine ⟨306696338552645739805787963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204464225701763826537191975 306696338552645739805787963)
    ·
      refine ⟨460044507828968609708681945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306696338552645739805787963 460044507828968609708681945)
      ·
        refine ⟨345033380871726457281511459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 460044507828968609708681945 345033380871726457281511459)
        ·
          refine ⟨517550071307589685922267189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345033380871726457281511459 517550071307589685922267189)
          ·
            refine ⟨48520319185086533055212549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 517550071307589685922267189 48520319185086533055212549)
            ·
              refine ⟨9097559847203724947852353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48520319185086533055212549 9097559847203724947852353)
              ·
                refine ⟨6823169885402793710889265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9097559847203724947852353 6823169885402793710889265)
                ·
                  refine ⟨5117377414052095283166949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6823169885402793710889265 5117377414052095283166949)
                  ·
                    refine ⟨959508265134767865593803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5117377414052095283166949 959508265134767865593803)
                    ·
                      rfl

theorem cell23_5605907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 2, 4].length) (baseStart_5605907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605907 prefixEnd_5605907 := by exact prefixLift 5605907
  have htrace : WordTrace (prefixWord ++ tailWord_5605907) baseStart_5605907 baseEnd_5605907 := by
    simpa [prefixWord, tailWord_5605907, baseEnd_5605907] using wordTrace_append hprefix tailTrace_5605907
  have hstable : (prefixWord ++ tailWord_5605907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605907).length < 2 ^ (prefixWord ++ tailWord_5605907).sum := by decide
  have hdescent : baseEnd_5605907 < baseStart_5605907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605908 : List Nat := [2, 4, 3, 1, 1, 2, 1, 4, 1, 1, 3]
def baseStart_5605908 : Nat := 118140960795 + 5605908 * 2 ^ 59
def prefixEnd_5605908 : Nat := 4983230072969 + 3 ^ 40 * 5605908 * 2
def baseEnd_5605908 : Nat := 2878525308884958092868905

theorem tailTrace_5605908 : CollatzResearch.WordTrace tailWord_5605908 prefixEnd_5605908 2878525308884958092868905 := by
  unfold tailWord_5605908
  simp only [CollatzResearch.WordTrace]
  refine ⟨102232131087380101853989189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136309508116506802471985585 102232131087380101853989189)
  ·
    refine ⟨19168524578883769097622973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102232131087380101853989189 19168524578883769097622973)
    ·
      refine ⟨7188196717081413411608615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19168524578883769097622973 7188196717081413411608615)
      ·
        refine ⟨10782295075622120117412923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7188196717081413411608615 10782295075622120117412923)
        ·
          refine ⟨16173442613433180176119385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10782295075622120117412923 16173442613433180176119385)
          ·
            refine ⟨12130081960074885132089539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16173442613433180176119385 12130081960074885132089539)
            ·
              refine ⟨18195122940112327698134309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12130081960074885132089539 18195122940112327698134309)
              ·
                refine ⟨3411585551271061443400183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18195122940112327698134309 3411585551271061443400183)
                ·
                  refine ⟨5117378326906592165100275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3411585551271061443400183 5117378326906592165100275)
                  ·
                    refine ⟨7676067490359888247650413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5117378326906592165100275 7676067490359888247650413)
                    ·
                      refine ⟨2878525308884958092868905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7676067490359888247650413 2878525308884958092868905)
                      ·
                        rfl

theorem cell23_5605908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_5605908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605908 prefixEnd_5605908 := by exact prefixLift 5605908
  have htrace : WordTrace (prefixWord ++ tailWord_5605908) baseStart_5605908 baseEnd_5605908 := by
    simpa [prefixWord, tailWord_5605908, baseEnd_5605908] using wordTrace_append hprefix tailTrace_5605908
  have hstable : (prefixWord ++ tailWord_5605908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605908).length < 2 ^ (prefixWord ++ tailWord_5605908).sum := by decide
  have hdescent : baseEnd_5605908 < baseStart_5605908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605917 : List Nat := [1, 4, 2, 2, 1, 2, 1, 2, 3, 2, 3]
def baseStart_5605917 : Nat := 118140960795 + 5605917 * 2 ^ 59
def prefixEnd_5605917 : Nat := 4983230072969 + 3 ^ 40 * 5605917 * 2
def baseEnd_5605917 : Nat := 2878529930210848557656363

theorem tailTrace_5605917 : CollatzResearch.WordTrace tailWord_5605917 prefixEnd_5605917 2878529930210848557656363 := by
  unfold tailWord_5605917
  simp only [CollatzResearch.WordTrace]
  refine ⟨204464590431727598245056005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136309726954485065496704003 204464590431727598245056005)
  ·
    refine ⟨38337110705948924670948001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204464590431727598245056005 38337110705948924670948001)
    ·
      refine ⟨28752833029461693503211001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38337110705948924670948001 28752833029461693503211001)
      ·
        refine ⟨21564624772096270127408251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28752833029461693503211001 21564624772096270127408251)
        ·
          refine ⟨32346937158144405191112377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21564624772096270127408251 32346937158144405191112377)
          ·
            refine ⟨24260202868608303893334283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32346937158144405191112377 24260202868608303893334283)
            ·
              refine ⟨36390304302912455840001425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24260202868608303893334283 36390304302912455840001425)
              ·
                refine ⟨27292728227184341880001069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36390304302912455840001425 27292728227184341880001069)
                ·
                  refine ⟨10234773085194128205000401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27292728227184341880001069 10234773085194128205000401)
                  ·
                    refine ⟨7676079813895596153750301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10234773085194128205000401 7676079813895596153750301)
                    ·
                      refine ⟨2878529930210848557656363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7676079813895596153750301 2878529930210848557656363)
                      ·
                        rfl

theorem cell23_5605917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_5605917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605917 prefixEnd_5605917 := by exact prefixLift 5605917
  have htrace : WordTrace (prefixWord ++ tailWord_5605917) baseStart_5605917 baseEnd_5605917 := by
    simpa [prefixWord, tailWord_5605917, baseEnd_5605917] using wordTrace_append hprefix tailTrace_5605917
  have hstable : (prefixWord ++ tailWord_5605917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605917).length < 2 ^ (prefixWord ++ tailWord_5605917).sum := by decide
  have hdescent : baseEnd_5605917 < baseStart_5605917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605924 : List Nat := [2, 3, 1, 5, 1, 1, 2, 1, 1, 6]
def baseStart_5605924 : Nat := 118140960795 + 5605924 * 2 ^ 59
def prefixEnd_5605924 : Nat := 4983230072969 + 3 ^ 40 * 5605924 * 2
def baseEnd_5605924 : Nat := 959511174858476676756277

theorem tailTrace_5605924 : CollatzResearch.WordTrace tailWord_5605924 prefixEnd_5605924 959511174858476676756277 := by
  unfold tailWord_5605924
  simp only [CollatzResearch.WordTrace]
  refine ⟨102232422871351119220280413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136309897161801492293707217 102232422871351119220280413)
  ·
    refine ⟨38337158576756669707605155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102232422871351119220280413 38337158576756669707605155)
    ·
      refine ⟨57505737865135004561407733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38337158576756669707605155 57505737865135004561407733)
      ·
        refine ⟨5391162924856406677631975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57505737865135004561407733 5391162924856406677631975)
        ·
          refine ⟨8086744387284610016447963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5391162924856406677631975 8086744387284610016447963)
          ·
            refine ⟨12130116580926915024671945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8086744387284610016447963 12130116580926915024671945)
            ·
              refine ⟨9097587435695186268503959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12130116580926915024671945 9097587435695186268503959)
              ·
                refine ⟨13646381153542779402755939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9097587435695186268503959 13646381153542779402755939)
                ·
                  refine ⟨20469571730314169104133909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13646381153542779402755939 20469571730314169104133909)
                  ·
                    refine ⟨959511174858476676756277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20469571730314169104133909 959511174858476676756277)
                    ·
                      rfl

theorem cell23_5605924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_5605924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605924 prefixEnd_5605924 := by exact prefixLift 5605924
  have htrace : WordTrace (prefixWord ++ tailWord_5605924) baseStart_5605924 baseEnd_5605924 := by
    simpa [prefixWord, tailWord_5605924, baseEnd_5605924] using wordTrace_append hprefix tailTrace_5605924
  have hstable : (prefixWord ++ tailWord_5605924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605924).length < 2 ^ (prefixWord ++ tailWord_5605924).sum := by decide
  have hdescent : baseEnd_5605924 < baseStart_5605924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605948 : List Nat := [2, 2, 2, 2, 3, 2, 2, 3, 1, 2, 2]
def baseStart_5605948 : Nat := 118140960795 + 5605948 * 2 ^ 59
def prefixEnd_5605948 : Nat := 4983230072969 + 3 ^ 40 * 5605948 * 2
def baseEnd_5605948 : Nat := 2878545848111137936368721

theorem tailTrace_5605948 : CollatzResearch.WordTrace tailWord_5605948 prefixEnd_5605948 2878545848111137936368721 := by
  unfold tailWord_5605948
  simp only [CollatzResearch.WordTrace]
  refine ⟨102232860547307645269717249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136310480729743527026289665 102232860547307645269717249)
  ·
    refine ⟨76674645410480733952287937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102232860547307645269717249 76674645410480733952287937)
    ·
      refine ⟨57505984057860550464215953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76674645410480733952287937 57505984057860550464215953)
      ·
        refine ⟨43129488043395412848161965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57505984057860550464215953 43129488043395412848161965)
        ·
          refine ⟨16173558016273279818060737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43129488043395412848161965 16173558016273279818060737)
          ·
            refine ⟨12130168512204959863545553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16173558016273279818060737 12130168512204959863545553)
            ·
              refine ⟨9097626384153719897659165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12130168512204959863545553 9097626384153719897659165)
              ·
                refine ⟨3411609894057644961622187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9097626384153719897659165 3411609894057644961622187)
                ·
                  refine ⟨5117414841086467442433281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3411609894057644961622187 5117414841086467442433281)
                  ·
                    refine ⟨3838061130814850581824961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5117414841086467442433281 3838061130814850581824961)
                    ·
                      refine ⟨2878545848111137936368721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3838061130814850581824961 2878545848111137936368721)
                      ·
                        rfl

theorem cell23_5605948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_5605948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605948 prefixEnd_5605948 := by exact prefixLift 5605948
  have htrace : WordTrace (prefixWord ++ tailWord_5605948) baseStart_5605948 baseEnd_5605948 := by
    simpa [prefixWord, tailWord_5605948, baseEnd_5605948] using wordTrace_append hprefix tailTrace_5605948
  have hstable : (prefixWord ++ tailWord_5605948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605948).length < 2 ^ (prefixWord ++ tailWord_5605948).sum := by decide
  have hdescent : baseEnd_5605948 < baseStart_5605948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5605958 : List Nat := [6, 1, 1, 1, 2, 3, 1, 2, 2, 4]
def baseStart_5605958 : Nat := 118140960795 + 5605958 * 2 ^ 59
def prefixEnd_5605958 : Nat := 4983230072969 + 3 ^ 40 * 5605958 * 2
def baseEnd_5605958 : Nat := 959516994305894299081225

theorem tailTrace_5605958 : CollatzResearch.WordTrace tailWord_5605958 prefixEnd_5605958 959516994305894299081225 := by
  unfold tailWord_5605958
  simp only [CollatzResearch.WordTrace]
  refine ⟨6389565182018095695228079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 136310723883052708164865685 6389565182018095695228079)
  ·
    refine ⟨9584347773027143542842119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6389565182018095695228079 9584347773027143542842119)
    ·
      refine ⟨14376521659540715314263179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9584347773027143542842119 14376521659540715314263179)
      ·
        refine ⟨21564782489311072971394769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14376521659540715314263179 21564782489311072971394769)
        ·
          refine ⟨16173586866983304728546077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21564782489311072971394769 16173586866983304728546077)
          ·
            refine ⟨6065095075118739273204779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16173586866983304728546077 6065095075118739273204779)
            ·
              refine ⟨9097642612678108909807169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6065095075118739273204779 9097642612678108909807169)
              ·
                refine ⟨6823231959508581682355377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9097642612678108909807169 6823231959508581682355377)
                ·
                  refine ⟨5117423969631436261766533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6823231959508581682355377 5117423969631436261766533)
                  ·
                    refine ⟨959516994305894299081225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5117423969631436261766533 959516994305894299081225)
                    ·
                      rfl

theorem cell23_5605958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_5605958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5605958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5605958 prefixEnd_5605958 := by exact prefixLift 5605958
  have htrace : WordTrace (prefixWord ++ tailWord_5605958) baseStart_5605958 baseEnd_5605958 := by
    simpa [prefixWord, tailWord_5605958, baseEnd_5605958] using wordTrace_append hprefix tailTrace_5605958
  have hstable : (prefixWord ++ tailWord_5605958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5605958).length < 2 ^ (prefixWord ++ tailWord_5605958).sum := by decide
  have hdescent : baseEnd_5605958 < baseStart_5605958 := by decide
  rcases family_descends (prefixWord ++ tailWord_5605958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606094 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2]
def baseStart_5606094 : Nat := 118140960795 + 5606094 * 2 ^ 59
def prefixEnd_5606094 : Nat := 4983230072969 + 3 ^ 40 * 5606094 * 2
def baseEnd_5606094 : Nat := 2878620816286694365143049

theorem tailTrace_5606094 : CollatzResearch.WordTrace tailWord_5606094 prefixEnd_5606094 2878620816286694365143049 := by
  unfold tailWord_5606094
  simp only [CollatzResearch.WordTrace]
  refine ⟨25558880769010794684281167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136314030768057571649499557 25558880769010794684281167)
  ·
    refine ⟨38338321153516192026421751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25558880769010794684281167 38338321153516192026421751)
    ·
      refine ⟨57507481730274288039632627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38338321153516192026421751 57507481730274288039632627)
      ·
        refine ⟨86261222595411432059448941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57507481730274288039632627 86261222595411432059448941)
        ·
          refine ⟨32347958473279287022293353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86261222595411432059448941 32347958473279287022293353)
          ·
            refine ⟨24260968854959465266720015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32347958473279287022293353 24260968854959465266720015)
            ·
              refine ⟨36391453282439197900080023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24260968854959465266720015 36391453282439197900080023)
              ·
                refine ⟨54587179923658796850120035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36391453282439197900080023 54587179923658796850120035)
                ·
                  refine ⟨81880769885488195275180053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54587179923658796850120035 81880769885488195275180053)
                  ·
                    refine ⟨3838161088382259153524065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81880769885488195275180053 3838161088382259153524065)
                    ·
                      refine ⟨2878620816286694365143049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3838161088382259153524065 2878620816286694365143049)
                      ·
                        rfl

theorem cell23_5606094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2].length) (baseStart_5606094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606094 prefixEnd_5606094 := by exact prefixLift 5606094
  have htrace : WordTrace (prefixWord ++ tailWord_5606094) baseStart_5606094 baseEnd_5606094 := by
    simpa [prefixWord, tailWord_5606094, baseEnd_5606094] using wordTrace_append hprefix tailTrace_5606094
  have hstable : (prefixWord ++ tailWord_5606094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606094).length < 2 ^ (prefixWord ++ tailWord_5606094).sum := by decide
  have hdescent : baseEnd_5606094 < baseStart_5606094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606097 : List Nat := [1, 2, 2, 1, 2, 3, 2, 2, 1, 4, 3]
def baseStart_5606097 : Nat := 118140960795 + 5606097 * 2 ^ 59
def prefixEnd_5606097 : Nat := 4983230072969 + 3 ^ 40 * 5606097 * 2
def baseEnd_5606097 : Nat := 2878622356728657853405535

theorem tailTrace_5606097 : CollatzResearch.WordTrace tailWord_5606097 prefixEnd_5606097 2878622356728657853405535 := by
  unfold tailWord_5606097
  simp only [CollatzResearch.WordTrace]
  refine ⟨204471155571075488986608545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136314103714050325991072363 204471155571075488986608545)
  ·
    refine ⟨153353366678306616739956409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204471155571075488986608545 153353366678306616739956409)
    ·
      refine ⟨115015025008729962554967307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153353366678306616739956409 115015025008729962554967307)
      ·
        refine ⟨172522537513094943832450961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115015025008729962554967307 172522537513094943832450961)
        ·
          refine ⟨129391903134821207874338221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172522537513094943832450961 129391903134821207874338221)
          ·
            refine ⟨48521963675557952952876833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129391903134821207874338221 48521963675557952952876833)
            ·
              refine ⟨36391472756668464714657625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48521963675557952952876833 36391472756668464714657625)
              ·
                refine ⟨27293604567501348535993219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36391472756668464714657625 27293604567501348535993219)
                ·
                  refine ⟨40940406851252022803989829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27293604567501348535993219 40940406851252022803989829)
                  ·
                    refine ⟨7676326284609754275748093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40940406851252022803989829 7676326284609754275748093)
                    ·
                      refine ⟨2878622356728657853405535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7676326284609754275748093 2878622356728657853405535)
                      ·
                        rfl

theorem cell23_5606097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 4, 3].length) (baseStart_5606097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606097 prefixEnd_5606097 := by exact prefixLift 5606097
  have htrace : WordTrace (prefixWord ++ tailWord_5606097) baseStart_5606097 baseEnd_5606097 := by
    simpa [prefixWord, tailWord_5606097, baseEnd_5606097] using wordTrace_append hprefix tailTrace_5606097
  have hstable : (prefixWord ++ tailWord_5606097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606097).length < 2 ^ (prefixWord ++ tailWord_5606097).sum := by decide
  have hdescent : baseEnd_5606097 < baseStart_5606097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606104 : List Nat := [2, 1, 2, 2, 3, 3, 1, 2, 3, 4]
def baseStart_5606104 : Nat := 118140960795 + 5606104 * 2 ^ 59
def prefixEnd_5606104 : Nat := 4983230072969 + 3 ^ 40 * 5606104 * 2
def baseEnd_5606104 : Nat := 959541983697746442006001

theorem tailTrace_5606104 : CollatzResearch.WordTrace tailWord_5606104 prefixEnd_5606104 959541983697746442006001 := by
  unfold tailWord_5606104
  simp only [CollatzResearch.WordTrace]
  refine ⟨102235705441025064591056683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136314273921366752788075577 102235705441025064591056683)
  ·
    refine ⟨153353558161537596886585025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102235705441025064591056683 153353558161537596886585025)
    ·
      refine ⟨115015168621153197664938769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153353558161537596886585025 115015168621153197664938769)
      ·
        refine ⟨86261376465864898248704077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115015168621153197664938769 86261376465864898248704077)
        ·
          refine ⟨32348016174699336843264029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86261376465864898248704077 32348016174699336843264029)
          ·
            refine ⟨12130506065512251316224011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32348016174699336843264029 12130506065512251316224011)
            ·
              refine ⟨18195759098268376974336017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12130506065512251316224011 18195759098268376974336017)
              ·
                refine ⟨13646819323701282730752013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18195759098268376974336017 13646819323701282730752013)
                ·
                  refine ⟨5117557246387981024032005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13646819323701282730752013 5117557246387981024032005)
                  ·
                    refine ⟨959541983697746442006001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5117557246387981024032005 959541983697746442006001)
                    ·
                      rfl

theorem cell23_5606104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 3, 4].length) (baseStart_5606104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606104 prefixEnd_5606104 := by exact prefixLift 5606104
  have htrace : WordTrace (prefixWord ++ tailWord_5606104) baseStart_5606104 baseEnd_5606104 := by
    simpa [prefixWord, tailWord_5606104, baseEnd_5606104] using wordTrace_append hprefix tailTrace_5606104
  have hstable : (prefixWord ++ tailWord_5606104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606104).length < 2 ^ (prefixWord ++ tailWord_5606104).sum := by decide
  have hdescent : baseEnd_5606104 < baseStart_5606104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606151 : List Nat := [1, 1, 4, 4, 1, 2, 3, 1, 6]
def baseStart_5606151 : Nat := 118140960795 + 5606151 * 2 ^ 59
def prefixEnd_5606151 : Nat := 4983230072969 + 3 ^ 40 * 5606151 * 2
def baseEnd_5606151 : Nat := 319850009409333404681143

theorem tailTrace_5606151 : CollatzResearch.WordTrace tailWord_5606151 prefixEnd_5606151 319850009409333404681143 := by
  unfold tailWord_5606151
  simp only [CollatzResearch.WordTrace]
  refine ⟨204473125112879856209074307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136315416741919904139382871 204473125112879856209074307)
  ·
    refine ⟨306709687669319784313611461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204473125112879856209074307 306709687669319784313611461)
    ·
      refine ⟨57508066437997459558802149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 306709687669319784313611461 57508066437997459558802149)
      ·
        refine ⟨10782762457124523667275403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57508066437997459558802149 10782762457124523667275403)
        ·
          refine ⟨16174143685686785500913105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10782762457124523667275403 16174143685686785500913105)
          ·
            refine ⟨12130607764265089125684829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16174143685686785500913105 12130607764265089125684829)
            ·
              refine ⟨4548977911599408422131811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12130607764265089125684829 4548977911599408422131811)
              ·
                refine ⟨6823466867399112633197717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4548977911599408422131811 6823466867399112633197717)
                ·
                  refine ⟨319850009409333404681143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6823466867399112633197717 319850009409333404681143)
                  ·
                    rfl

theorem cell23_5606151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 6].length) (baseStart_5606151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606151 prefixEnd_5606151 := by exact prefixLift 5606151
  have htrace : WordTrace (prefixWord ++ tailWord_5606151) baseStart_5606151 baseEnd_5606151 := by
    simpa [prefixWord, tailWord_5606151, baseEnd_5606151] using wordTrace_append hprefix tailTrace_5606151
  have hstable : (prefixWord ++ tailWord_5606151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606151).length < 2 ^ (prefixWord ++ tailWord_5606151).sum := by decide
  have hdescent : baseEnd_5606151 < baseStart_5606151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606154 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 3, 5, 2]
def baseStart_5606154 : Nat := 118140960795 + 5606154 * 2 ^ 59
def prefixEnd_5606154 : Nat := 4983230072969 + 3 ^ 40 * 5606154 * 2
def baseEnd_5606154 : Nat := 2878651625125964130392773

theorem tailTrace_5606154 : CollatzResearch.WordTrace tailWord_5606154 prefixEnd_5606154 2878651625125964130392773 := by
  unfold tailWord_5606154
  simp only [CollatzResearch.WordTrace]
  refine ⟨51118308632967246930358379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136315489687912658480955677 51118308632967246930358379)
  ·
    refine ⟨76677462949450870395537569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51118308632967246930358379 76677462949450870395537569)
    ·
      refine ⟨57508097212088152796653177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76677462949450870395537569 57508097212088152796653177)
      ·
        refine ⟨43131072909066114597489883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57508097212088152796653177 43131072909066114597489883)
        ·
          refine ⟨64696609363599171896234825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43131072909066114597489883 64696609363599171896234825)
          ·
            refine ⟨48522457022699378922176119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64696609363599171896234825 48522457022699378922176119)
            ·
              refine ⟨72783685534049068383264179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48522457022699378922176119 72783685534049068383264179)
              ·
                refine ⟨109175528301073602574896269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72783685534049068383264179 109175528301073602574896269)
                ·
                  refine ⟨40940823112902600965586101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109175528301073602574896269 40940823112902600965586101)
                  ·
                    refine ⟨3838202166834618840523697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40940823112902600965586101 3838202166834618840523697)
                    ·
                      refine ⟨2878651625125964130392773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3838202166834618840523697 2878651625125964130392773)
                      ·
                        rfl

theorem cell23_5606154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_5606154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606154 prefixEnd_5606154 := by exact prefixLift 5606154
  have htrace : WordTrace (prefixWord ++ tailWord_5606154) baseStart_5606154 baseEnd_5606154 := by
    simpa [prefixWord, tailWord_5606154, baseEnd_5606154] using wordTrace_append hprefix tailTrace_5606154
  have hstable : (prefixWord ++ tailWord_5606154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606154).length < 2 ^ (prefixWord ++ tailWord_5606154).sum := by decide
  have hdescent : baseEnd_5606154 < baseStart_5606154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
