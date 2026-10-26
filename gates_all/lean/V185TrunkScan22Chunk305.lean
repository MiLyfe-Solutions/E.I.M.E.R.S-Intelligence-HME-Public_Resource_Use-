import V185TrunkScan22Chunk304

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2720434 : List Nat := [3, 2, 1, 1, 1, 2, 1, 4, 2, 5]
def baseStart_2720434 : Nat := 118140960795 + 2720434 * 2 ^ 59
def prefixEnd_2720434 : Nat := 4983230072969 + 3 ^ 40 * 2720434 * 2
def baseEnd_2720434 : Nat := 931260153889009682109305

theorem tailTrace_2720434 : CollatzResearch.WordTrace tailWord_2720434 prefixEnd_2720434 931260153889009682109305 := by
  unfold tailWord_2720434
  simp only [CollatzResearch.WordTrace]
  refine ⟨24805594856584926495642089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66148252950893137321712237 24805594856584926495642089)
  ·
    refine ⟨18604196142438694871731567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24805594856584926495642089 18604196142438694871731567)
    ·
      refine ⟨27906294213658042307597351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18604196142438694871731567 27906294213658042307597351)
      ·
        refine ⟨41859441320487063461396027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27906294213658042307597351 41859441320487063461396027)
        ·
          refine ⟨62789161980730595192094041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41859441320487063461396027 62789161980730595192094041)
          ·
            refine ⟨47091871485547946394070531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62789161980730595192094041 47091871485547946394070531)
            ·
              refine ⟨70637807228321919591105797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47091871485547946394070531 70637807228321919591105797)
              ·
                refine ⟨13244588855310359923332337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70637807228321919591105797 13244588855310359923332337)
                ·
                  refine ⟨9933441641482769942499253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13244588855310359923332337 9933441641482769942499253)
                  ·
                    refine ⟨931260153889009682109305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9933441641482769942499253 931260153889009682109305)
                    ·
                      rfl

theorem cell22_2720434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_2720434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2720434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2720434 prefixEnd_2720434 := by exact prefixLift 2720434
  have htrace : WordTrace (prefixWord ++ tailWord_2720434) baseStart_2720434 baseEnd_2720434 := by
    simpa [prefixWord, tailWord_2720434, baseEnd_2720434] using wordTrace_append hprefix tailTrace_2720434
  have hstable : (prefixWord ++ tailWord_2720434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720434).length < 2 ^ (prefixWord ++ tailWord_2720434).sum := by decide
  have hdescent : baseEnd_2720434 < baseStart_2720434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720483 : List Nat := [1, 1, 1, 7, 1, 2, 1, 3, 1, 4]
def baseStart_2720483 : Nat := 118140960795 + 2720483 * 2 ^ 59
def prefixEnd_2720483 : Nat := 4983230072969 + 3 ^ 40 * 2720483 * 2
def baseEnd_2720483 : Nat := 931276927590389887634155

theorem tailTrace_2720483 : CollatzResearch.WordTrace tailWord_2720483 prefixEnd_2720483 931276927590389887634155 := by
  unfold tailWord_2720483
  simp only [CollatzResearch.WordTrace]
  refine ⟨99224166603162187351102103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66149444402108124900734735 99224166603162187351102103)
  ·
    refine ⟨148836249904743281026653155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99224166603162187351102103 148836249904743281026653155)
    ·
      refine ⟨223254374857114921539979733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148836249904743281026653155 223254374857114921539979733)
      ·
        refine ⟨5232524410713630973593275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 223254374857114921539979733 5232524410713630973593275)
        ·
          refine ⟨7848786616070446460389913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5232524410713630973593275 7848786616070446460389913)
          ·
            refine ⟨5886589962052834845292435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7848786616070446460389913 5886589962052834845292435)
            ·
              refine ⟨8829884943079252267938653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5886589962052834845292435 8829884943079252267938653)
              ·
                refine ⟨3311206853654719600476995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8829884943079252267938653 3311206853654719600476995)
                ·
                  refine ⟨4966810280482079400715493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3311206853654719600476995 4966810280482079400715493)
                  ·
                    refine ⟨931276927590389887634155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4966810280482079400715493 931276927590389887634155)
                    ·
                      rfl

theorem cell22_2720483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 4].length) (baseStart_2720483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2720483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2720483 prefixEnd_2720483 := by exact prefixLift 2720483
  have htrace : WordTrace (prefixWord ++ tailWord_2720483) baseStart_2720483 baseEnd_2720483 := by
    simpa [prefixWord, tailWord_2720483, baseEnd_2720483] using wordTrace_append hprefix tailTrace_2720483
  have hstable : (prefixWord ++ tailWord_2720483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720483).length < 2 ^ (prefixWord ++ tailWord_2720483).sum := by decide
  have hdescent : baseEnd_2720483 < baseStart_2720483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720496 : List Nat := [2, 1, 1, 1, 3, 1, 5, 1, 4, 3]
def baseStart_2720496 : Nat := 118140960795 + 2720496 * 2 ^ 59
def prefixEnd_2720496 : Nat := 4983230072969 + 3 ^ 40 * 2720496 * 2
def baseEnd_2720496 : Nat := 931281377756062187059115

theorem tailTrace_2720496 : CollatzResearch.WordTrace tailWord_2720496 prefixEnd_2720496 931281377756062187059115 := by
  unfold tailWord_2720496
  simp only [CollatzResearch.WordTrace]
  refine ⟨49612320376057545285662671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66149760501410060380883561 49612320376057545285662671)
  ·
    refine ⟨74418480564086317928494007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49612320376057545285662671 74418480564086317928494007)
    ·
      refine ⟨111627720846129476892741011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74418480564086317928494007 111627720846129476892741011)
      ·
        refine ⟨167441581269194215339111517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111627720846129476892741011 167441581269194215339111517)
        ·
          refine ⟨62790592975947830752166819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167441581269194215339111517 62790592975947830752166819)
          ·
            refine ⟨94185889463921746128250229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62790592975947830752166819 94185889463921746128250229)
            ·
              refine ⟨8829927137242663699523459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94185889463921746128250229 8829927137242663699523459)
              ·
                refine ⟨13244890705863995549285189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8829927137242663699523459 13244890705863995549285189)
                ·
                  refine ⟨2483417007349499165490973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13244890705863995549285189 2483417007349499165490973)
                  ·
                    refine ⟨931281377756062187059115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2483417007349499165490973 931281377756062187059115)
                    ·
                      rfl

theorem cell22_2720496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 4, 3].length) (baseStart_2720496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2720496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2720496 prefixEnd_2720496 := by exact prefixLift 2720496
  have htrace : WordTrace (prefixWord ++ tailWord_2720496) baseStart_2720496 baseEnd_2720496 := by
    simpa [prefixWord, tailWord_2720496, baseEnd_2720496] using wordTrace_append hprefix tailTrace_2720496
  have hstable : (prefixWord ++ tailWord_2720496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720496).length < 2 ^ (prefixWord ++ tailWord_2720496).sum := by decide
  have hdescent : baseEnd_2720496 < baseStart_2720496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720498 : List Nat := [3, 2, 1, 3, 1, 2, 2, 4, 4]
def baseStart_2720498 : Nat := 118140960795 + 2720498 * 2 ^ 59
def prefixEnd_2720498 : Nat := 4983230072969 + 3 ^ 40 * 2720498 * 2
def baseEnd_2720498 : Nat := 310427354132311616169703

theorem tailTrace_2720498 : CollatzResearch.WordTrace tailWord_2720498 prefixEnd_2720498 310427354132311616169703 := by
  unfold tailWord_2720498
  simp only [CollatzResearch.WordTrace]
  refine ⟨24806178424526961228224537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66149809132071896608598765 24806178424526961228224537)
  ·
    refine ⟨18604633818395220921168403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24806178424526961228224537 18604633818395220921168403)
    ·
      refine ⟨27906950727592831381752605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18604633818395220921168403 27906950727592831381752605)
      ·
        refine ⟨10465106522847311768157227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27906950727592831381752605 10465106522847311768157227)
        ·
          refine ⟨15697659784270967652235841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10465106522847311768157227 15697659784270967652235841)
          ·
            refine ⟨11773244838203225739176881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15697659784270967652235841 11773244838203225739176881)
            ·
              refine ⟨8829933628652419304382661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11773244838203225739176881 8829933628652419304382661)
              ·
                refine ⟨1655612555372328619571749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8829933628652419304382661 1655612555372328619571749)
                ·
                  refine ⟨310427354132311616169703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1655612555372328619571749 310427354132311616169703)
                  ·
                    rfl

theorem cell22_2720498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_2720498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2720498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2720498 prefixEnd_2720498 := by exact prefixLift 2720498
  have htrace : WordTrace (prefixWord ++ tailWord_2720498) baseStart_2720498 baseEnd_2720498 := by
    simpa [prefixWord, tailWord_2720498, baseEnd_2720498] using wordTrace_append hprefix tailTrace_2720498
  have hstable : (prefixWord ++ tailWord_2720498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720498).length < 2 ^ (prefixWord ++ tailWord_2720498).sum := by decide
  have hdescent : baseEnd_2720498 < baseStart_2720498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720509 : List Nat := [1, 4, 1, 1, 1, 1, 4, 9]
def baseStart_2720509 : Nat := 118140960795 + 2720509 * 2 ^ 59
def prefixEnd_2720509 : Nat := 4983230072969 + 3 ^ 40 * 2720509 * 2
def baseEnd_2720509 : Nat := 103476203102414942942675

theorem tailTrace_2720509 : CollatzResearch.WordTrace tailWord_2720509 prefixEnd_2720509 103476203102414942942675 := by
  unfold tailWord_2720509
  simp only [CollatzResearch.WordTrace]
  refine ⟨99225114901067993791548581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66150076600711995861032387 99225114901067993791548581)
  ·
    refine ⟨18604709043950248835915359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99225114901067993791548581 18604709043950248835915359)
    ·
      refine ⟨27907063565925373253873039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18604709043950248835915359 27907063565925373253873039)
      ·
        refine ⟨41860595348888059880809559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27907063565925373253873039 41860595348888059880809559)
        ·
          refine ⟨62790893023332089821214339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41860595348888059880809559 62790893023332089821214339)
          ·
            refine ⟨94186339534998134731821509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62790893023332089821214339 94186339534998134731821509)
            ·
              refine ⟨17659938662812150262216533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94186339534998134731821509 17659938662812150262216533)
              ·
                refine ⟨103476203102414942942675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17659938662812150262216533 103476203102414942942675)
                ·
                  rfl

theorem cell22_2720509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 9].length) (baseStart_2720509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2720509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2720509 prefixEnd_2720509 := by exact prefixLift 2720509
  have htrace : WordTrace (prefixWord ++ tailWord_2720509) baseStart_2720509 baseEnd_2720509 := by
    simpa [prefixWord, tailWord_2720509, baseEnd_2720509] using wordTrace_append hprefix tailTrace_2720509
  have hstable : (prefixWord ++ tailWord_2720509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720509).length < 2 ^ (prefixWord ++ tailWord_2720509).sum := by decide
  have hdescent : baseEnd_2720509 < baseStart_2720509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720524 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 1, 9]
def baseStart_2720524 : Nat := 118140960795 + 2720524 * 2 ^ 59
def prefixEnd_2720524 : Nat := 4983230072969 + 3 ^ 40 * 2720524 * 2
def baseEnd_2720524 : Nat := 931290962728279447359029

theorem tailTrace_2720524 : CollatzResearch.WordTrace tailWord_2720524 prefixEnd_2720524 931290962728279447359029 := by
  unfold tailWord_2720524
  simp only [CollatzResearch.WordTrace]
  refine ⟨49612830998006825676672313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66150441330675767568896417 49612830998006825676672313)
  ·
    refine ⟨37209623248505119257504235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49612830998006825676672313 37209623248505119257504235)
    ·
      refine ⟨55814434872757678886256353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37209623248505119257504235 55814434872757678886256353)
      ·
        refine ⟨41860826154568259164692265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55814434872757678886256353 41860826154568259164692265)
        ·
          refine ⟨31395619615926194373519199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41860826154568259164692265 31395619615926194373519199)
          ·
            refine ⟨47093429423889291560278799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31395619615926194373519199 47093429423889291560278799)
            ·
              refine ⟨70640144135833937340418199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47093429423889291560278799 70640144135833937340418199)
              ·
                refine ⟨105960216203750906010627299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70640144135833937340418199 105960216203750906010627299)
                ·
                  refine ⟨158940324305626359015940949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105960216203750906010627299 158940324305626359015940949)
                  ·
                    refine ⟨931290962728279447359029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 158940324305626359015940949 931290962728279447359029)
                    ·
                      rfl

theorem cell22_2720524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_2720524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2720524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2720524 prefixEnd_2720524 := by exact prefixLift 2720524
  have htrace : WordTrace (prefixWord ++ tailWord_2720524) baseStart_2720524 baseEnd_2720524 := by
    simpa [prefixWord, tailWord_2720524, baseEnd_2720524] using wordTrace_append hprefix tailTrace_2720524
  have hstable : (prefixWord ++ tailWord_2720524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720524).length < 2 ^ (prefixWord ++ tailWord_2720524).sum := by decide
  have hdescent : baseEnd_2720524 < baseStart_2720524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720564 : List Nat := [2, 5, 1, 1, 3, 2, 2, 1, 2, 3]
def baseStart_2720564 : Nat := 118140960795 + 2720564 * 2 ^ 59
def prefixEnd_2720564 : Nat := 4983230072969 + 3 ^ 40 * 2720564 * 2
def baseEnd_2720564 : Nat := 931304655545732676358907

theorem tailTrace_2720564 : CollatzResearch.WordTrace tailWord_2720564 prefixEnd_2720564 931304655545732676358907 := by
  unfold tailWord_2720564
  simp only [CollatzResearch.WordTrace]
  refine ⟨49613560457934369092400373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66151413943912492123200497 49613560457934369092400373)
  ·
    refine ⟨4651271292931347102412535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49613560457934369092400373 4651271292931347102412535)
    ·
      refine ⟨6976906939397020653618803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4651271292931347102412535 6976906939397020653618803)
      ·
        refine ⟨10465360409095530980428205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6976906939397020653618803 10465360409095530980428205)
        ·
          refine ⟨3924510153410824117660577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10465360409095530980428205 3924510153410824117660577)
          ·
            refine ⟨2943382615058118088245433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3924510153410824117660577 2943382615058118088245433)
            ·
              refine ⟨2207536961293588566184075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2943382615058118088245433 2207536961293588566184075)
              ·
                refine ⟨3311305441940382849276113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2207536961293588566184075 3311305441940382849276113)
                ·
                  refine ⟨2483479081455287136957085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3311305441940382849276113 2483479081455287136957085)
                  ·
                    refine ⟨931304655545732676358907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2483479081455287136957085 931304655545732676358907)
                    ·
                      rfl

theorem cell22_2720564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_2720564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2720564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2720564 prefixEnd_2720564 := by exact prefixLift 2720564
  have htrace : WordTrace (prefixWord ++ tailWord_2720564) baseStart_2720564 baseEnd_2720564 := by
    simpa [prefixWord, tailWord_2720564, baseEnd_2720564] using wordTrace_append hprefix tailTrace_2720564
  have hstable : (prefixWord ++ tailWord_2720564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720564).length < 2 ^ (prefixWord ++ tailWord_2720564).sum := by decide
  have hdescent : baseEnd_2720564 < baseStart_2720564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720648 : List Nat := [2, 1, 3, 3, 2, 1, 2, 2, 1, 5]
def baseStart_2720648 : Nat := 118140960795 + 2720648 * 2 ^ 59
def prefixEnd_2720648 : Nat := 4983230072969 + 3 ^ 40 * 2720648 * 2
def baseEnd_2720648 : Nat := 931333410462384457258649

theorem tailTrace_2720648 : CollatzResearch.WordTrace tailWord_2720648 prefixEnd_2720648 931333410462384457258649 := by
  unfold tailWord_2720648
  simp only [CollatzResearch.WordTrace]
  refine ⟨49615092323782210265429299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66153456431709613687239065 49615092323782210265429299)
  ·
    refine ⟨74422638485673315398143949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49615092323782210265429299 74422638485673315398143949)
    ·
      refine ⟨27908489432127493274303981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74422638485673315398143949 27908489432127493274303981)
      ·
        refine ⟨10465683537047809977863993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27908489432127493274303981 10465683537047809977863993)
        ·
          refine ⟨7849262652785857483397995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10465683537047809977863993 7849262652785857483397995)
          ·
            refine ⟨11773893979178786225096993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7849262652785857483397995 11773893979178786225096993)
            ·
              refine ⟨8830420484384089668822745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11773893979178786225096993 8830420484384089668822745)
              ·
                refine ⟨6622815363288067251617059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8830420484384089668822745 6622815363288067251617059)
                ·
                  refine ⟨9934223044932100877425589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6622815363288067251617059 9934223044932100877425589)
                  ·
                    refine ⟨931333410462384457258649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9934223044932100877425589 931333410462384457258649)
                    ·
                      rfl

theorem cell22_2720648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_2720648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2720648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2720648 prefixEnd_2720648 := by exact prefixLift 2720648
  have htrace : WordTrace (prefixWord ++ tailWord_2720648) baseStart_2720648 baseEnd_2720648 := by
    simpa [prefixWord, tailWord_2720648, baseEnd_2720648] using wordTrace_append hprefix tailTrace_2720648
  have hstable : (prefixWord ++ tailWord_2720648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720648).length < 2 ^ (prefixWord ++ tailWord_2720648).sum := by decide
  have hdescent : baseEnd_2720648 < baseStart_2720648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720650 : List Nat := [3, 1, 2, 4, 1, 1, 1, 5, 4]
def baseStart_2720650 : Nat := 118140960795 + 2720650 * 2 ^ 59
def prefixEnd_2720650 : Nat := 4983230072969 + 3 ^ 40 * 2720650 * 2
def baseEnd_2720650 : Nat := 310444698367752372902881

theorem tailTrace_2720650 : CollatzResearch.WordTrace tailWord_2720650 prefixEnd_2720650 310444698367752372902881 := by
  unfold tailWord_2720650
  simp only [CollatzResearch.WordTrace]
  refine ⟨24807564398389293718107851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66153505062371449914954269 24807564398389293718107851)
  ·
    refine ⟨37211346597583940577161777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24807564398389293718107851 37211346597583940577161777)
    ·
      refine ⟨27908509948187955432871333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37211346597583940577161777 27908509948187955432871333)
      ·
        refine ⟨5232845615285241643663375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27908509948187955432871333 5232845615285241643663375)
        ·
          refine ⟨7849268422927862465495063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5232845615285241643663375 7849268422927862465495063)
          ·
            refine ⟨11773902634391793698242595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7849268422927862465495063 11773902634391793698242595)
            ·
              refine ⟨17660853951587690547363893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11773902634391793698242595 17660853951587690547363893)
              ·
                refine ⟨1655705057961345988815365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17660853951587690547363893 1655705057961345988815365)
                ·
                  refine ⟨310444698367752372902881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1655705057961345988815365 310444698367752372902881)
                  ·
                    rfl

theorem cell22_2720650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 5, 4].length) (baseStart_2720650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2720650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2720650 prefixEnd_2720650 := by exact prefixLift 2720650
  have htrace : WordTrace (prefixWord ++ tailWord_2720650) baseStart_2720650 baseEnd_2720650 := by
    simpa [prefixWord, tailWord_2720650, baseEnd_2720650] using wordTrace_append hprefix tailTrace_2720650
  have hstable : (prefixWord ++ tailWord_2720650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720650).length < 2 ^ (prefixWord ++ tailWord_2720650).sum := by decide
  have hdescent : baseEnd_2720650 < baseStart_2720650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720661 : List Nat := [1, 3, 2, 1, 1, 5, 9]
def baseStart_2720661 : Nat := 118140960795 + 2720661 * 2 ^ 59
def prefixEnd_2720661 : Nat := 4983230072969 + 3 ^ 40 * 2720661 * 2
def baseEnd_2720661 : Nat := 34493994838076176173467

theorem tailTrace_2720661 : CollatzResearch.WordTrace tailWord_2720661 prefixEnd_2720661 34493994838076176173467 := by
  unfold tailWord_2720661
  simp only [CollatzResearch.WordTrace]
  refine ⟨99230658796517323751081837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66153772531011549167387891 99230658796517323751081837)
  ·
    refine ⟨37211497048693996406655689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99230658796517323751081837 37211497048693996406655689)
    ·
      refine ⟨27908622786520497304991767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37211497048693996406655689 27908622786520497304991767)
      ·
        refine ⟨41862934179780745957487651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27908622786520497304991767 41862934179780745957487651)
        ·
          refine ⟨62794401269671118936231477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41862934179780745957487651 62794401269671118936231477)
          ·
            refine ⟨5886975119031667400271701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62794401269671118936231477 5886975119031667400271701)
            ·
              refine ⟨34493994838076176173467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5886975119031667400271701 34493994838076176173467)
              ·
                rfl

theorem cell22_2720661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 9].length) (baseStart_2720661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2720661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2720661 prefixEnd_2720661 := by exact prefixLift 2720661
  have htrace : WordTrace (prefixWord ++ tailWord_2720661) baseStart_2720661 baseEnd_2720661 := by
    simpa [prefixWord, tailWord_2720661, baseEnd_2720661] using wordTrace_append hprefix tailTrace_2720661
  have hstable : (prefixWord ++ tailWord_2720661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720661).length < 2 ^ (prefixWord ++ tailWord_2720661).sum := by decide
  have hdescent : baseEnd_2720661 < baseStart_2720661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720736 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 1, 10]
def baseStart_2720736 : Nat := 118140960795 + 2720736 * 2 ^ 59
def prefixEnd_2720736 : Nat := 4983230072969 + 3 ^ 40 * 2720736 * 2
def baseEnd_2720736 : Nat := 931363534660781561058379

theorem tailTrace_2720736 : CollatzResearch.WordTrace tailWord_2720736 prefixEnd_2720736 931363534660781561058379 := by
  unfold tailWord_2720736
  simp only [CollatzResearch.WordTrace]
  refine ⟨49616697135622805780031031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66155596180830407706708041 49616697135622805780031031)
  ·
    refine ⟨74425045703434208670046547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49616697135622805780031031 74425045703434208670046547)
    ·
      refine ⟨111637568555151313005069821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74425045703434208670046547 111637568555151313005069821)
      ·
        refine ⟨41864088208181742376901183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111637568555151313005069821 41864088208181742376901183)
        ·
          refine ⟨62796132312272613565351775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41864088208181742376901183 62796132312272613565351775)
          ·
            refine ⟨94194198468408920348027663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62796132312272613565351775 94194198468408920348027663)
            ·
              refine ⟨141291297702613380522041495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94194198468408920348027663 141291297702613380522041495)
              ·
                refine ⟨211936946553920070783062243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141291297702613380522041495 211936946553920070783062243)
                ·
                  refine ⟨317905419830880106174593365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211936946553920070783062243 317905419830880106174593365)
                  ·
                    refine ⟨931363534660781561058379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 317905419830880106174593365 931363534660781561058379)
                    ·
                      rfl

theorem cell22_2720736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 10].length) (baseStart_2720736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2720736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2720736 prefixEnd_2720736 := by exact prefixLift 2720736
  have htrace : WordTrace (prefixWord ++ tailWord_2720736) baseStart_2720736 baseEnd_2720736 := by
    simpa [prefixWord, tailWord_2720736, baseEnd_2720736] using wordTrace_append hprefix tailTrace_2720736
  have hstable : (prefixWord ++ tailWord_2720736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720736).length < 2 ^ (prefixWord ++ tailWord_2720736).sum := by decide
  have hdescent : baseEnd_2720736 < baseStart_2720736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720830 : List Nat := [4, 2, 1, 3, 1, 2, 9]
def baseStart_2720830 : Nat := 118140960795 + 2720830 * 2 ^ 59
def prefixEnd_2720830 : Nat := 4983230072969 + 3 ^ 40 * 2720830 * 2
def baseEnd_2720830 : Nat := 34496137510436912933633

theorem tailTrace_2720830 : CollatzResearch.WordTrace tailWord_2720830 prefixEnd_2720830 34496137510436912933633 := by
  unfold tailWord_2720830
  simp only [CollatzResearch.WordTrace]
  refine ⟨12404602841613133201747993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66157881821936710409322629 12404602841613133201747993)
  ·
    refine ⟨9303452131209849901310995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12404602841613133201747993 9303452131209849901310995)
    ·
      refine ⟨13955178196814774851966493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9303452131209849901310995 13955178196814774851966493)
      ·
        refine ⟨5233191823805540569487435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13955178196814774851966493 5233191823805540569487435)
        ·
          refine ⟨7849787735708310854231153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5233191823805540569487435 7849787735708310854231153)
          ·
            refine ⟨5887340801781233140673365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7849787735708310854231153 5887340801781233140673365)
            ·
              refine ⟨34496137510436912933633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5887340801781233140673365 34496137510436912933633)
              ·
                rfl

theorem cell22_2720830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 9].length) (baseStart_2720830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2720830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2720830 prefixEnd_2720830 := by exact prefixLift 2720830
  have htrace : WordTrace (prefixWord ++ tailWord_2720830) baseStart_2720830 baseEnd_2720830 := by
    simpa [prefixWord, tailWord_2720830, baseEnd_2720830] using wordTrace_append hprefix tailTrace_2720830
  have hstable : (prefixWord ++ tailWord_2720830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720830).length < 2 ^ (prefixWord ++ tailWord_2720830).sum := by decide
  have hdescent : baseEnd_2720830 < baseStart_2720830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720922 : List Nat := [3, 1, 1, 5, 1, 2, 1, 1, 3, 4]
def baseStart_2720922 : Nat := 118140960795 + 2720922 * 2 ^ 59
def prefixEnd_2720922 : Nat := 4983230072969 + 3 ^ 40 * 2720922 * 2
def baseEnd_2720922 : Nat := 931427206261939075907809

theorem tailTrace_2720922 : CollatzResearch.WordTrace tailWord_2720922 prefixEnd_2720922 931427206261939075907809 := by
  unfold tailWord_2720922
  simp only [CollatzResearch.WordTrace]
  refine ⟨24810044562142941331583255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66160118832381176884222013 24810044562142941331583255)
  ·
    refine ⟨37215066843214411997374883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24810044562142941331583255 37215066843214411997374883)
    ·
      refine ⟨55822600264821617996062325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37215066843214411997374883 55822600264821617996062325)
      ·
        refine ⟨5233368774827026687130843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55822600264821617996062325 5233368774827026687130843)
        ·
          refine ⟨7850053162240540030696265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5233368774827026687130843 7850053162240540030696265)
          ·
            refine ⟨5887539871680405023022199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7850053162240540030696265 5887539871680405023022199)
            ·
              refine ⟨8831309807520607534533299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5887539871680405023022199 8831309807520607534533299)
              ·
                refine ⟨13246964711280911301799949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8831309807520607534533299 13246964711280911301799949)
                ·
                  refine ⟨4967611766730341738174981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13246964711280911301799949 4967611766730341738174981)
                  ·
                    refine ⟨931427206261939075907809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4967611766730341738174981 931427206261939075907809)
                    ·
                      rfl

theorem cell22_2720922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_2720922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2720922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2720922 prefixEnd_2720922 := by exact prefixLift 2720922
  have htrace : WordTrace (prefixWord ++ tailWord_2720922) baseStart_2720922 baseEnd_2720922 := by
    simpa [prefixWord, tailWord_2720922, baseEnd_2720922] using wordTrace_append hprefix tailTrace_2720922
  have hstable : (prefixWord ++ tailWord_2720922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720922).length < 2 ^ (prefixWord ++ tailWord_2720922).sum := by decide
  have hdescent : baseEnd_2720922 < baseStart_2720922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720984 : List Nat := [2, 1, 2, 2, 5, 2, 1, 1, 2, 4]
def baseStart_2720984 : Nat := 118140960795 + 2720984 * 2 ^ 59
def prefixEnd_2720984 : Nat := 4983230072969 + 3 ^ 40 * 2720984 * 2
def baseEnd_2720984 : Nat := 931448430128991580857619

theorem tailTrace_2720984 : CollatzResearch.WordTrace tailWord_2720984 prefixEnd_2720984 931448430128991580857619 := by
  unfold tailWord_2720984
  simp only [CollatzResearch.WordTrace]
  refine ⟨49621219787173574957545003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66161626382898099943393337 49621219787173574957545003)
  ·
    refine ⟨74431829680760362436317505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49621219787173574957545003 74431829680760362436317505)
    ·
      refine ⟨55823872260570271827238129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74431829680760362436317505 55823872260570271827238129)
      ·
        refine ⟨41867904195427703870428597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55823872260570271827238129 41867904195427703870428597)
        ·
          refine ⟨3925116018321347237852681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41867904195427703870428597 3925116018321347237852681)
          ·
            refine ⟨2943837013741010428389511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3925116018321347237852681 2943837013741010428389511)
            ·
              refine ⟨4415755520611515642584267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2943837013741010428389511 4415755520611515642584267)
              ·
                refine ⟨6623633280917273463876401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4415755520611515642584267 6623633280917273463876401)
                ·
                  refine ⟨4967724960687955097907301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6623633280917273463876401 4967724960687955097907301)
                  ·
                    refine ⟨931448430128991580857619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4967724960687955097907301 931448430128991580857619)
                    ·
                      rfl

theorem cell22_2720984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 2, 4].length) (baseStart_2720984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2720984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2720984 prefixEnd_2720984 := by exact prefixLift 2720984
  have htrace : WordTrace (prefixWord ++ tailWord_2720984) baseStart_2720984 baseEnd_2720984 := by
    simpa [prefixWord, tailWord_2720984, baseEnd_2720984] using wordTrace_append hprefix tailTrace_2720984
  have hstable : (prefixWord ++ tailWord_2720984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720984).length < 2 ^ (prefixWord ++ tailWord_2720984).sum := by decide
  have hdescent : baseEnd_2720984 < baseStart_2720984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721040 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 9, 4]
def baseStart_2721040 : Nat := 118140960795 + 2721040 * 2 ^ 59
def prefixEnd_2721040 : Nat := 4983230072969 + 3 ^ 40 * 2721040 * 2
def baseEnd_2721040 : Nat := 931467600073426101457447

theorem tailTrace_2721040 : CollatzResearch.WordTrace tailWord_2721040 prefixEnd_2721040 931467600073426101457447 := by
  unfold tailWord_2721040
  simp only [CollatzResearch.WordTrace]
  refine ⟨49622241031072135739564287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66162988041429514319419049 49622241031072135739564287)
  ·
    refine ⟨74433361546608203609346431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49622241031072135739564287 74433361546608203609346431)
    ·
      refine ⟨111650042319912305414019647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74433361546608203609346431 111650042319912305414019647)
      ·
        refine ⟨167475063479868458121029471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111650042319912305414019647 167475063479868458121029471)
        ·
          refine ⟨251212595219802687181544207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167475063479868458121029471 251212595219802687181544207)
          ·
            refine ⟨376818892829704030772316311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251212595219802687181544207 376818892829704030772316311)
            ·
              refine ⟨565228339244556046158474467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376818892829704030772316311 565228339244556046158474467)
              ·
                refine ⟨847842508866834069237711701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 565228339244556046158474467 847842508866834069237711701)
                ·
                  refine ⟨4967827200391605874439717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 847842508866834069237711701 4967827200391605874439717)
                  ·
                    refine ⟨931467600073426101457447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4967827200391605874439717 931467600073426101457447)
                    ·
                      rfl

theorem cell22_2721040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 9, 4].length) (baseStart_2721040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2721040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2721040 prefixEnd_2721040 := by exact prefixLift 2721040
  have htrace : WordTrace (prefixWord ++ tailWord_2721040) baseStart_2721040 baseEnd_2721040 := by
    simpa [prefixWord, tailWord_2721040, baseEnd_2721040] using wordTrace_append hprefix tailTrace_2721040
  have hstable : (prefixWord ++ tailWord_2721040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721040).length < 2 ^ (prefixWord ++ tailWord_2721040).sum := by decide
  have hdescent : baseEnd_2721040 < baseStart_2721040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721149 : List Nat := [1, 4, 1, 1, 2, 2, 3, 2, 3, 3]
def baseStart_2721149 : Nat := 118140960795 + 2721149 * 2 ^ 59
def prefixEnd_2721149 : Nat := 4983230072969 + 3 ^ 40 * 2721149 * 2
def baseEnd_2721149 : Nat := 931504913000986150482113

theorem tailTrace_2721149 : CollatzResearch.WordTrace tailWord_2721149 prefixEnd_2721149 931504913000986150482113 := by
  unfold tailWord_2721149
  simp only [CollatzResearch.WordTrace]
  refine ⟨99248457618749383094846501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66165638412499588729897667 99248457618749383094846501)
  ·
    refine ⟨18609085803515509330283719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99248457618749383094846501 18609085803515509330283719)
    ·
      refine ⟨27913628705273263995425579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18609085803515509330283719 27913628705273263995425579)
      ·
        refine ⟨41870443057909895993138369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27913628705273263995425579 41870443057909895993138369)
        ·
          refine ⟨31402832293432421994853777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41870443057909895993138369 31402832293432421994853777)
          ·
            refine ⟨23552124220074316496140333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31402832293432421994853777 23552124220074316496140333)
            ·
              refine ⟨8832046582527868686052625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23552124220074316496140333 8832046582527868686052625)
              ·
                refine ⟨6624034936895901514539469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8832046582527868686052625 6624034936895901514539469)
                ·
                  refine ⟨2484013101335963067952301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6624034936895901514539469 2484013101335963067952301)
                  ·
                    refine ⟨931504913000986150482113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2484013101335963067952301 931504913000986150482113)
                    ·
                      rfl

theorem cell22_2721149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_2721149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2721149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2721149 prefixEnd_2721149 := by exact prefixLift 2721149
  have htrace : WordTrace (prefixWord ++ tailWord_2721149) baseStart_2721149 baseEnd_2721149 := by
    simpa [prefixWord, tailWord_2721149, baseEnd_2721149] using wordTrace_append hprefix tailTrace_2721149
  have hstable : (prefixWord ++ tailWord_2721149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721149).length < 2 ^ (prefixWord ++ tailWord_2721149).sum := by decide
  have hdescent : baseEnd_2721149 < baseStart_2721149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721153 : List Nat := [1, 2, 4, 3, 3, 1, 1, 1, 2, 4]
def baseStart_2721153 : Nat := 118140960795 + 2721153 * 2 ^ 59
def prefixEnd_2721153 : Nat := 4983230072969 + 3 ^ 40 * 2721153 * 2
def baseEnd_2721153 : Nat := 931506282282731473382101

theorem tailTrace_2721153 : CollatzResearch.WordTrace tailWord_2721153 prefixEnd_2721153 931506282282731473382101 := by
  unfold tailWord_2721153
  simp only [CollatzResearch.WordTrace]
  refine ⟨99248603510734891777992113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66165735673823261185328075 99248603510734891777992113)
  ·
    refine ⟨74436452633051168833494085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99248603510734891777992113 74436452633051168833494085)
    ·
      refine ⟨13956834868697094156280141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74436452633051168833494085 13956834868697094156280141)
      ·
        refine ⟨5233813075761410308605053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13956834868697094156280141 5233813075761410308605053)
        ·
          refine ⟨1962679903410528865726895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5233813075761410308605053 1962679903410528865726895)
          ·
            refine ⟨2944019855115793298590343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1962679903410528865726895 2944019855115793298590343)
            ·
              refine ⟨4416029782673689947885515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2944019855115793298590343 4416029782673689947885515)
              ·
                refine ⟨6624044674010534921828273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4416029782673689947885515 6624044674010534921828273)
                ·
                  refine ⟨4968033505507901191371205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6624044674010534921828273 4968033505507901191371205)
                  ·
                    refine ⟨931506282282731473382101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4968033505507901191371205 931506282282731473382101)
                    ·
                      rfl

theorem cell22_2721153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_2721153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2721153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2721153 prefixEnd_2721153 := by exact prefixLift 2721153
  have htrace : WordTrace (prefixWord ++ tailWord_2721153) baseStart_2721153 baseEnd_2721153 := by
    simpa [prefixWord, tailWord_2721153, baseEnd_2721153] using wordTrace_append hprefix tailTrace_2721153
  have hstable : (prefixWord ++ tailWord_2721153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721153).length < 2 ^ (prefixWord ++ tailWord_2721153).sum := by decide
  have hdescent : baseEnd_2721153 < baseStart_2721153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721177 : List Nat := [1, 2, 1, 2, 1, 5, 1, 2, 2, 5]
def baseStart_2721177 : Nat := 118140960795 + 2721177 * 2 ^ 59
def prefixEnd_2721177 : Nat := 4983230072969 + 3 ^ 40 * 2721177 * 2
def baseEnd_2721177 : Nat := 931514497973203410782027

theorem tailTrace_2721177 : CollatzResearch.WordTrace tailWord_2721177 prefixEnd_2721177 931514497973203410782027 := by
  unfold tailWord_2721177
  simp only [CollatzResearch.WordTrace]
  refine ⟨99249478862647943876865785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66166319241765295917910523 99249478862647943876865785)
  ·
    refine ⟨74437109146985957907649339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99249478862647943876865785 74437109146985957907649339)
    ·
      refine ⟨111655663720478936861474009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74437109146985957907649339 111655663720478936861474009)
      ·
        refine ⟨83741747790359202646105507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111655663720478936861474009 83741747790359202646105507)
        ·
          refine ⟨125612621685538803969158261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83741747790359202646105507 125612621685538803969158261)
          ·
            refine ⟨11776183283019262872108587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125612621685538803969158261 11776183283019262872108587)
            ·
              refine ⟨17664274924528894308162881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11776183283019262872108587 17664274924528894308162881)
              ·
                refine ⟨13248206193396670731122161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17664274924528894308162881 13248206193396670731122161)
                ·
                  refine ⟨9936154645047503048341621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13248206193396670731122161 9936154645047503048341621)
                  ·
                    refine ⟨931514497973203410782027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9936154645047503048341621 931514497973203410782027)
                    ·
                      rfl

theorem cell22_2721177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 5].length) (baseStart_2721177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2721177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2721177 prefixEnd_2721177 := by exact prefixLift 2721177
  have htrace : WordTrace (prefixWord ++ tailWord_2721177) baseStart_2721177 baseEnd_2721177 := by
    simpa [prefixWord, tailWord_2721177, baseEnd_2721177] using wordTrace_append hprefix tailTrace_2721177
  have hstable : (prefixWord ++ tailWord_2721177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721177).length < 2 ^ (prefixWord ++ tailWord_2721177).sum := by decide
  have hdescent : baseEnd_2721177 < baseStart_2721177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721207 : List Nat := [1, 1, 3, 1, 3, 2, 1, 4, 6]
def baseStart_2721207 : Nat := 118140960795 + 2721207 * 2 ^ 59
def prefixEnd_2721207 : Nat := 4983230072969 + 3 ^ 40 * 2721207 * 2
def baseEnd_2721207 : Nat := 310508255862097777510645

theorem tailTrace_2721207 : CollatzResearch.WordTrace tailWord_2721207 prefixEnd_2721207 310508255862097777510645 := by
  unfold tailWord_2721207
  simp only [CollatzResearch.WordTrace]
  refine ⟨99250573052539259000457875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66167048701692839333638583 99250573052539259000457875)
  ·
    refine ⟨148875859578808888500686813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99250573052539259000457875 148875859578808888500686813)
    ·
      refine ⟨55828447342053333187757555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148875859578808888500686813 55828447342053333187757555)
      ·
        refine ⟨83742671013079999781636333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55828447342053333187757555 83742671013079999781636333)
        ·
          refine ⟨31403501629904999918113625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83742671013079999781636333 31403501629904999918113625)
          ·
            refine ⟨23552626222428749938585219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31403501629904999918113625 23552626222428749938585219)
            ·
              refine ⟨35328939333643124907877829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23552626222428749938585219 35328939333643124907877829)
              ·
                refine ⟨6624176125058085920227093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35328939333643124907877829 6624176125058085920227093)
                ·
                  refine ⟨310508255862097777510645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6624176125058085920227093 310508255862097777510645)
                  ·
                    rfl

theorem cell22_2721207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 6].length) (baseStart_2721207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2721207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2721207 prefixEnd_2721207 := by exact prefixLift 2721207
  have htrace : WordTrace (prefixWord ++ tailWord_2721207) baseStart_2721207 baseEnd_2721207 := by
    simpa [prefixWord, tailWord_2721207, baseEnd_2721207] using wordTrace_append hprefix tailTrace_2721207
  have hstable : (prefixWord ++ tailWord_2721207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721207).length < 2 ^ (prefixWord ++ tailWord_2721207).sum := by decide
  have hdescent : baseEnd_2721207 < baseStart_2721207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721256 : List Nat := [2, 1, 4, 1, 1, 2, 3, 3, 2, 3]
def baseStart_2721256 : Nat := 118140960795 + 2721256 * 2 ^ 59
def prefixEnd_2721256 : Nat := 4983230072969 + 3 ^ 40 * 2721256 * 2
def baseEnd_2721256 : Nat := 931541541287673538056785

theorem tailTrace_2721256 : CollatzResearch.WordTrace tailWord_2721256 prefixEnd_2721256 931541541287673538056785 := by
  unfold tailWord_2721256
  simp only [CollatzResearch.WordTrace]
  refine ⟨49626180114680870184495811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66168240152907826912661081 49626180114680870184495811)
  ·
    refine ⟨74439270172021305276743717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49626180114680870184495811 74439270172021305276743717)
    ·
      refine ⟨13957363157253994739389447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74439270172021305276743717 13957363157253994739389447)
      ·
        refine ⟨20936044735880992109084171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13957363157253994739389447 20936044735880992109084171)
        ·
          refine ⟨31404067103821488163626257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20936044735880992109084171 31404067103821488163626257)
          ·
            refine ⟨23553050327866116122719693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31404067103821488163626257 23553050327866116122719693)
            ·
              refine ⟨8832393872949793546019885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23553050327866116122719693 8832393872949793546019885)
              ·
                refine ⟨3312147702356172579757457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8832393872949793546019885 3312147702356172579757457)
                ·
                  refine ⟨2484110776767129434818093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3312147702356172579757457 2484110776767129434818093)
                  ·
                    refine ⟨931541541287673538056785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2484110776767129434818093 931541541287673538056785)
                    ·
                      rfl

theorem cell22_2721256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_2721256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2721256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2721256 prefixEnd_2721256 := by exact prefixLift 2721256
  have htrace : WordTrace (prefixWord ++ tailWord_2721256) baseStart_2721256 baseEnd_2721256 := by
    simpa [prefixWord, tailWord_2721256, baseEnd_2721256] using wordTrace_append hprefix tailTrace_2721256
  have hstable : (prefixWord ++ tailWord_2721256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721256).length < 2 ^ (prefixWord ++ tailWord_2721256).sum := by decide
  have hdescent : baseEnd_2721256 < baseStart_2721256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721464 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 3, 7]
def baseStart_2721464 : Nat := 118140960795 + 2721464 * 2 ^ 59
def prefixEnd_2721464 : Nat := 4983230072969 + 3 ^ 40 * 2721464 * 2
def baseEnd_2721464 : Nat := 931612743938430328856147

theorem tailTrace_2721464 : CollatzResearch.WordTrace tailWord_2721464 prefixEnd_2721464 931612743938430328856147 := by
  unfold tailWord_2721464
  simp only [CollatzResearch.WordTrace]
  refine ⟨49629973306304095946281723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66173297741738794595042297 49629973306304095946281723)
  ·
    refine ⟨74444959959456143919422585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49629973306304095946281723 74444959959456143919422585)
    ·
      refine ⟨55833719969592107939566939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74444959959456143919422585 55833719969592107939566939)
      ·
        refine ⟨83750579954388161909350409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55833719969592107939566939 83750579954388161909350409)
        ·
          refine ⟨62812934965791121432012807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83750579954388161909350409 62812934965791121432012807)
          ·
            refine ⟨94219402448686682148019211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62812934965791121432012807 94219402448686682148019211)
            ·
              refine ⟨141329103673030023222028817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94219402448686682148019211 141329103673030023222028817)
              ·
                refine ⟨105996827754772517416521613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141329103673030023222028817 105996827754772517416521613)
                ·
                  refine ⟨39748810408039694031195605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105996827754772517416521613 39748810408039694031195605)
                  ·
                    refine ⟨931612743938430328856147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39748810408039694031195605 931612743938430328856147)
                    ·
                      rfl

theorem cell22_2721464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_2721464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2721464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2721464 prefixEnd_2721464 := by exact prefixLift 2721464
  have htrace : WordTrace (prefixWord ++ tailWord_2721464) baseStart_2721464 baseEnd_2721464 := by
    simpa [prefixWord, tailWord_2721464, baseEnd_2721464] using wordTrace_append hprefix tailTrace_2721464
  have hstable : (prefixWord ++ tailWord_2721464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721464).length < 2 ^ (prefixWord ++ tailWord_2721464).sum := by decide
  have hdescent : baseEnd_2721464 < baseStart_2721464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721466 : List Nat := [3, 1, 1, 1, 2, 4, 1, 4, 5]
def baseStart_2721466 : Nat := 118140960795 + 2721466 * 2 ^ 59
def prefixEnd_2721466 : Nat := 4983230072969 + 3 ^ 40 * 2721466 * 2
def baseEnd_2721466 : Nat := 310537809526434330102047

theorem tailTrace_2721466 : CollatzResearch.WordTrace tailWord_2721466 prefixEnd_2721466 310537809526434330102047 := by
  unfold tailWord_2721466
  simp only [CollatzResearch.WordTrace]
  refine ⟨24815004889650236558534063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66173346372400630822757501 24815004889650236558534063)
  ·
    refine ⟨37222507334475354837801095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24815004889650236558534063 37222507334475354837801095)
    ·
      refine ⟨55833761001713032256701643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37222507334475354837801095 55833761001713032256701643)
      ·
        refine ⟨83750641502569548385052465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55833761001713032256701643 83750641502569548385052465)
        ·
          refine ⟨62812981126927161288789349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83750641502569548385052465 62812981126927161288789349)
          ·
            refine ⟨11777433961298842741648003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62812981126927161288789349 11777433961298842741648003)
            ·
              refine ⟨17666150941948264112472005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11777433961298842741648003 17666150941948264112472005)
              ·
                refine ⟨3312403301615299521088501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17666150941948264112472005 3312403301615299521088501)
                ·
                  refine ⟨310537809526434330102047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3312403301615299521088501 310537809526434330102047)
                  ·
                    rfl

theorem cell22_2721466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 5].length) (baseStart_2721466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2721466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2721466 prefixEnd_2721466 := by exact prefixLift 2721466
  have htrace : WordTrace (prefixWord ++ tailWord_2721466) baseStart_2721466 baseEnd_2721466 := by
    simpa [prefixWord, tailWord_2721466, baseEnd_2721466] using wordTrace_append hprefix tailTrace_2721466
  have hstable : (prefixWord ++ tailWord_2721466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721466).length < 2 ^ (prefixWord ++ tailWord_2721466).sum := by decide
  have hdescent : baseEnd_2721466 < baseStart_2721466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721496 : List Nat := [2, 1, 2, 2, 3, 1, 1, 3, 3, 4]
def baseStart_2721496 : Nat := 118140960795 + 2721496 * 2 ^ 59
def prefixEnd_2721496 : Nat := 4983230072969 + 3 ^ 40 * 2721496 * 2
def baseEnd_2721496 : Nat := 931623698192392912056049

theorem tailTrace_2721496 : CollatzResearch.WordTrace tailWord_2721496 prefixEnd_2721496 931623698192392912056049 := by
  unfold tailWord_2721496
  simp only [CollatzResearch.WordTrace]
  refine ⟨49630556874246130678864171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66174075832328174238485561 49630556874246130678864171)
  ·
    refine ⟨74445835311369196018296257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49630556874246130678864171 74445835311369196018296257)
    ·
      refine ⟨55834376483526897013722193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74445835311369196018296257 55834376483526897013722193)
      ·
        refine ⟨41875782362645172760291645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55834376483526897013722193 41875782362645172760291645)
        ·
          refine ⟨15703418385991939785109367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41875782362645172760291645 15703418385991939785109367)
          ·
            refine ⟨23555127578987909677664051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15703418385991939785109367 23555127578987909677664051)
            ·
              refine ⟨35332691368481864516496077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23555127578987909677664051 35332691368481864516496077)
              ·
                refine ⟨13249759263180699193686029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35332691368481864516496077 13249759263180699193686029)
                ·
                  refine ⟨4968659723692762197632261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13249759263180699193686029 4968659723692762197632261)
                  ·
                    refine ⟨931623698192392912056049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4968659723692762197632261 931623698192392912056049)
                    ·
                      rfl

theorem cell22_2721496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_2721496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2721496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2721496 prefixEnd_2721496 := by exact prefixLift 2721496
  have htrace : WordTrace (prefixWord ++ tailWord_2721496) baseStart_2721496 baseEnd_2721496 := by
    simpa [prefixWord, tailWord_2721496, baseEnd_2721496] using wordTrace_append hprefix tailTrace_2721496
  have hstable : (prefixWord ++ tailWord_2721496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721496).length < 2 ^ (prefixWord ++ tailWord_2721496).sum := by decide
  have hdescent : baseEnd_2721496 < baseStart_2721496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721590 : List Nat := [5, 1, 2, 2, 1, 2, 2, 7]
def baseStart_2721590 : Nat := 118140960795 + 2721590 * 2 ^ 59
def prefixEnd_2721590 : Nat := 4983230072969 + 3 ^ 40 * 2721590 * 2
def baseEnd_2721590 : Nat := 103517319590378666689529

theorem tailTrace_2721590 : CollatzResearch.WordTrace tailWord_2721590 prefixEnd_2721590 103517319590378666689529 := by
  unfold tailWord_2721590
  simp only [CollatzResearch.WordTrace]
  refine ⟨6204033888134482213228139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66176361473434476941100149 6204033888134482213228139)
  ·
    refine ⟨9306050832201723319842209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6204033888134482213228139 9306050832201723319842209)
    ·
      refine ⟨6979538124151292489881657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9306050832201723319842209 6979538124151292489881657)
      ·
        refine ⟨5234653593113469367411243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6979538124151292489881657 5234653593113469367411243)
        ·
          refine ⟨7851980389670204051116865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5234653593113469367411243 7851980389670204051116865)
          ·
            refine ⟨5888985292252653038337649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7851980389670204051116865 5888985292252653038337649)
            ·
              refine ⟨4416738969189489778753237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5888985292252653038337649 4416738969189489778753237)
              ·
                refine ⟨103517319590378666689529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4416738969189489778753237 103517319590378666689529)
                ·
                  rfl

theorem cell22_2721590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_2721590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2721590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2721590 prefixEnd_2721590 := by exact prefixLift 2721590
  have htrace : WordTrace (prefixWord ++ tailWord_2721590) baseStart_2721590 baseEnd_2721590 := by
    simpa [prefixWord, tailWord_2721590, baseEnd_2721590] using wordTrace_append hprefix tailTrace_2721590
  have hstable : (prefixWord ++ tailWord_2721590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721590).length < 2 ^ (prefixWord ++ tailWord_2721590).sum := by decide
  have hdescent : baseEnd_2721590 < baseStart_2721590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721616 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 4, 5]
def baseStart_2721616 : Nat := 118140960795 + 2721616 * 2 ^ 59
def prefixEnd_2721616 : Nat := 4983230072969 + 3 ^ 40 * 2721616 * 2
def baseEnd_2721616 : Nat := 931664776644752599055681

theorem tailTrace_2721616 : CollatzResearch.WordTrace tailWord_2721616 prefixEnd_2721616 931664776644752599055681 := by
  unfold tailWord_2721616
  simp only [CollatzResearch.WordTrace]
  refine ⟨49632745254028760926048351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66176993672038347901397801 49632745254028760926048351)
  ·
    refine ⟨74449117881043141389072527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49632745254028760926048351 74449117881043141389072527)
    ·
      refine ⟨111673676821564712083608791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74449117881043141389072527 111673676821564712083608791)
      ·
        refine ⟨167510515232347068125413187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111673676821564712083608791 167510515232347068125413187)
        ·
          refine ⟨251265772848520602188119781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167510515232347068125413187 251265772848520602188119781)
          ·
            refine ⟨47112332409097612910272459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 251265772848520602188119781 47112332409097612910272459)
            ·
              refine ⟨70668498613646419365408689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47112332409097612910272459 70668498613646419365408689)
              ·
                refine ⟨53001373960234814524056517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70668498613646419365408689 53001373960234814524056517)
                ·
                  refine ⟨9937757617544027723260597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53001373960234814524056517 9937757617544027723260597)
                  ·
                    refine ⟨931664776644752599055681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9937757617544027723260597 931664776644752599055681)
                    ·
                      rfl

theorem cell22_2721616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 4, 5].length) (baseStart_2721616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2721616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2721616 prefixEnd_2721616 := by exact prefixLift 2721616
  have htrace : WordTrace (prefixWord ++ tailWord_2721616) baseStart_2721616 baseEnd_2721616 := by
    simpa [prefixWord, tailWord_2721616, baseEnd_2721616] using wordTrace_append hprefix tailTrace_2721616
  have hstable : (prefixWord ++ tailWord_2721616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721616).length < 2 ^ (prefixWord ++ tailWord_2721616).sum := by decide
  have hdescent : baseEnd_2721616 < baseStart_2721616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721635 : List Nat := [1, 1, 1, 5, 4, 1, 2, 2, 5]
def baseStart_2721635 : Nat := 118140960795 + 2721635 * 2 ^ 59
def prefixEnd_2721635 : Nat := 4983230072969 + 3 ^ 40 * 2721635 * 2
def baseEnd_2721635 : Nat := 310557093577680960943541

theorem tailTrace_2721635 : CollatzResearch.WordTrace tailWord_2721635 prefixEnd_2721635 310557093577680960943541 := by
  unfold tailWord_2721635
  simp only [CollatzResearch.WordTrace]
  refine ⟨99266183494988688097038359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66177455663325792064692239 99266183494988688097038359)
  ·
    refine ⟨148899275242483032145557539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99266183494988688097038359 148899275242483032145557539)
    ·
      refine ⟨223348912863724548218336309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148899275242483032145557539 223348912863724548218336309)
      ·
        refine ⟨20938960580974176395469029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 223348912863724548218336309 20938960580974176395469029)
        ·
          refine ⟨3926055108932658074150443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20938960580974176395469029 3926055108932658074150443)
          ·
            refine ⟨5889082663398987111225665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3926055108932658074150443 5889082663398987111225665)
            ·
              refine ⟨4416811997549240333419249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5889082663398987111225665 4416811997549240333419249)
              ·
                refine ⟨3312608998161930250064437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4416811997549240333419249 3312608998161930250064437)
                ·
                  refine ⟨310557093577680960943541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3312608998161930250064437 310557093577680960943541)
                  ·
                    rfl

theorem cell22_2721635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 5].length) (baseStart_2721635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2721635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2721635 prefixEnd_2721635 := by exact prefixLift 2721635
  have htrace : WordTrace (prefixWord ++ tailWord_2721635) baseStart_2721635 baseEnd_2721635 := by
    simpa [prefixWord, tailWord_2721635, baseEnd_2721635] using wordTrace_append hprefix tailTrace_2721635
  have hstable : (prefixWord ++ tailWord_2721635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721635).length < 2 ^ (prefixWord ++ tailWord_2721635).sum := by decide
  have hdescent : baseEnd_2721635 < baseStart_2721635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721682 : List Nat := [3, 2, 3, 2, 1, 2, 1, 3, 1, 4]
def baseStart_2721682 : Nat := 118140960795 + 2721682 * 2 ^ 59
def prefixEnd_2721682 : Nat := 4983230072969 + 3 ^ 40 * 2721682 * 2
def baseEnd_2721682 : Nat := 931687369793550426905479

theorem tailTrace_2721682 : CollatzResearch.WordTrace tailWord_2721682 prefixEnd_2721682 931687369793550426905479 := by
  unfold tailWord_2721682
  simp only [CollatzResearch.WordTrace]
  refine ⟨24816974431454603780999825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66178598483878943415999533 24816974431454603780999825)
  ·
    refine ⟨18612730823590952835749869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24816974431454603780999825 18612730823590952835749869)
    ·
      refine ⟨6979774058846607313406201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18612730823590952835749869 6979774058846607313406201)
      ·
        refine ⟨5234830544134955485054651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6979774058846607313406201 5234830544134955485054651)
        ·
          refine ⟨7852245816202433227581977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5234830544134955485054651 7852245816202433227581977)
          ·
            refine ⟨5889184362151824920686483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7852245816202433227581977 5889184362151824920686483)
            ·
              refine ⟨8833776543227737381029725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5889184362151824920686483 8833776543227737381029725)
              ·
                refine ⟨3312666203710401517886147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8833776543227737381029725 3312666203710401517886147)
                ·
                  refine ⟨4968999305565602276829221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3312666203710401517886147 4968999305565602276829221)
                  ·
                    refine ⟨931687369793550426905479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4968999305565602276829221 931687369793550426905479)
                    ·
                      rfl

theorem cell22_2721682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_2721682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2721682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2721682 prefixEnd_2721682 := by exact prefixLift 2721682
  have htrace : WordTrace (prefixWord ++ tailWord_2721682) baseStart_2721682 baseEnd_2721682 := by
    simpa [prefixWord, tailWord_2721682, baseEnd_2721682] using wordTrace_append hprefix tailTrace_2721682
  have hstable : (prefixWord ++ tailWord_2721682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721682).length < 2 ^ (prefixWord ++ tailWord_2721682).sum := by decide
  have hdescent : baseEnd_2721682 < baseStart_2721682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721686 : List Nat := [5, 3, 1, 1, 2, 2, 1, 2, 5]
def baseStart_2721686 : Nat := 118140960795 + 2721686 * 2 ^ 59
def prefixEnd_2721686 : Nat := 4983230072969 + 3 ^ 40 * 2721686 * 2
def baseEnd_2721686 : Nat := 310562913025098583268489

theorem tailTrace_2721686 : CollatzResearch.WordTrace tailWord_2721686 prefixEnd_2721686 310562913025098583268489 := by
  unfold tailWord_2721686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6204252726112745237946557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66178695745202615871429941 6204252726112745237946557)
  ·
    refine ⟨2326594772292279464229959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6204252726112745237946557 2326594772292279464229959)
    ·
      refine ⟨3489892158438419196344939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2326594772292279464229959 3489892158438419196344939)
      ·
        refine ⟨5234838237657628794517409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3489892158438419196344939 5234838237657628794517409)
        ·
          refine ⟨3926128678243221595888057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5234838237657628794517409 3926128678243221595888057)
          ·
            refine ⟨2944596508682416196916043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3926128678243221595888057 2944596508682416196916043)
            ·
              refine ⟨4416894763023624295374065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2944596508682416196916043 4416894763023624295374065)
              ·
                refine ⟨3312671072267718221530549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4416894763023624295374065 3312671072267718221530549)
                ·
                  refine ⟨310562913025098583268489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3312671072267718221530549 310562913025098583268489)
                  ·
                    rfl

theorem cell22_2721686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_2721686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2721686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2721686 prefixEnd_2721686 := by exact prefixLift 2721686
  have htrace : WordTrace (prefixWord ++ tailWord_2721686) baseStart_2721686 baseEnd_2721686 := by
    simpa [prefixWord, tailWord_2721686, baseEnd_2721686] using wordTrace_append hprefix tailTrace_2721686
  have hstable : (prefixWord ++ tailWord_2721686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721686).length < 2 ^ (prefixWord ++ tailWord_2721686).sum := by decide
  have hdescent : baseEnd_2721686 < baseStart_2721686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721725 : List Nat := [1, 4, 1, 2, 3, 1, 4, 6]
def baseStart_2721725 : Nat := 118140960795 + 2721725 * 2 ^ 59
def prefixEnd_2721725 : Nat := 4983230072969 + 3 ^ 40 * 2721725 * 2
def baseEnd_2721725 : Nat := 103522454396923627564483

theorem tailTrace_2721725 : CollatzResearch.WordTrace tailWord_2721725 prefixEnd_2721725 103522454396923627564483 := by
  unfold tailWord_2721725
  simp only [CollatzResearch.WordTrace]
  refine ⟨99269466064662633467814629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66179644043108422311876419 99269466064662633467814629)
  ·
    refine ⟨18613024887124243775215243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99269466064662633467814629 18613024887124243775215243)
    ·
      refine ⟨27919537330686365662822865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18613024887124243775215243 27919537330686365662822865)
      ·
        refine ⟨20939652998014774247117149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27919537330686365662822865 20939652998014774247117149)
        ·
          refine ⟨7852369874255540342668931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20939652998014774247117149 7852369874255540342668931)
          ·
            refine ⟨11778554811383310514003397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7852369874255540342668931 11778554811383310514003397)
            ·
              refine ⟨2208479027134370721375637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11778554811383310514003397 2208479027134370721375637)
              ·
                refine ⟨103522454396923627564483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2208479027134370721375637 103522454396923627564483)
                ·
                  rfl

theorem cell22_2721725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 6].length) (baseStart_2721725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2721725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2721725 prefixEnd_2721725 := by exact prefixLift 2721725
  have htrace : WordTrace (prefixWord ++ tailWord_2721725) baseStart_2721725 baseEnd_2721725 := by
    simpa [prefixWord, tailWord_2721725, baseEnd_2721725] using wordTrace_append hprefix tailTrace_2721725
  have hstable : (prefixWord ++ tailWord_2721725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721725).length < 2 ^ (prefixWord ++ tailWord_2721725).sum := by decide
  have hdescent : baseEnd_2721725 < baseStart_2721725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721768 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 1, 7]
def baseStart_2721768 : Nat := 118140960795 + 2721768 * 2 ^ 59
def prefixEnd_2721768 : Nat := 4983230072969 + 3 ^ 40 * 2721768 * 2
def baseEnd_2721768 : Nat := 931716809351074869255215

theorem tailTrace_2721768 : CollatzResearch.WordTrace tailWord_2721768 prefixEnd_2721768 931716809351074869255215 := by
  unfold tailWord_2721768
  simp only [CollatzResearch.WordTrace]
  refine ⟨49635517201753425905814979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66180689602337901207753305 49635517201753425905814979)
  ·
    refine ⟨74453275802630138858722469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49635517201753425905814979 74453275802630138858722469)
    ·
      refine ⟨13959989212993151036010463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74453275802630138858722469 13959989212993151036010463)
      ·
        refine ⟨20939983819489726554015695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13959989212993151036010463 20939983819489726554015695)
        ·
          refine ⟨31409975729234589831023543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20939983819489726554015695 31409975729234589831023543)
          ·
            refine ⟨47114963593851884746535315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31409975729234589831023543 47114963593851884746535315)
            ·
              refine ⟨70672445390777827119802973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47114963593851884746535315 70672445390777827119802973)
              ·
                refine ⟨26502167021541685169926115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70672445390777827119802973 26502167021541685169926115)
                ·
                  refine ⟨39753250532312527754889173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26502167021541685169926115 39753250532312527754889173)
                  ·
                    refine ⟨931716809351074869255215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39753250532312527754889173 931716809351074869255215)
                    ·
                      rfl

theorem cell22_2721768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_2721768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2721768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2721768 prefixEnd_2721768 := by exact prefixLift 2721768
  have htrace : WordTrace (prefixWord ++ tailWord_2721768) baseStart_2721768 baseEnd_2721768 := by
    simpa [prefixWord, tailWord_2721768, baseEnd_2721768] using wordTrace_append hprefix tailTrace_2721768
  have hstable : (prefixWord ++ tailWord_2721768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721768).length < 2 ^ (prefixWord ++ tailWord_2721768).sum := by decide
  have hdescent : baseEnd_2721768 < baseStart_2721768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721770 : List Nat := [3, 1, 3, 1, 2, 1, 3, 3, 5]
def baseStart_2721770 : Nat := 118140960795 + 2721770 * 2 ^ 59
def prefixEnd_2721770 : Nat := 4983230072969 + 3 ^ 40 * 2721770 * 2
def baseEnd_2721770 : Nat := 310572497997315843568403

theorem tailTrace_2721770 : CollatzResearch.WordTrace tailWord_2721770 prefixEnd_2721770 310572497997315843568403 := by
  unfold tailWord_2721770
  simp only [CollatzResearch.WordTrace]
  refine ⟨24817776837374901538300691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66180738232999737435468509 24817776837374901538300691)
  ·
    refine ⟨37226665256062352307451037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24817776837374901538300691 37226665256062352307451037)
    ·
      refine ⟨13959999471023382115294139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37226665256062352307451037 13959999471023382115294139)
      ·
        refine ⟨20939999206535073172941209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13959999471023382115294139 20939999206535073172941209)
        ·
          refine ⟨15704999404901304879705907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20939999206535073172941209 15704999404901304879705907)
          ·
            refine ⟨23557499107351957319558861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15704999404901304879705907 23557499107351957319558861)
            ·
              refine ⟨8834062165256983994834573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23557499107351957319558861 8834062165256983994834573)
              ·
                refine ⟨3312773311971368998062965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8834062165256983994834573 3312773311971368998062965)
                ·
                  refine ⟨310572497997315843568403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3312773311971368998062965 310572497997315843568403)
                  ·
                    rfl

theorem cell22_2721770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 5].length) (baseStart_2721770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2721770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2721770 prefixEnd_2721770 := by exact prefixLift 2721770
  have htrace : WordTrace (prefixWord ++ tailWord_2721770) baseStart_2721770 baseEnd_2721770 := by
    simpa [prefixWord, tailWord_2721770, baseEnd_2721770] using wordTrace_append hprefix tailTrace_2721770
  have hstable : (prefixWord ++ tailWord_2721770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721770).length < 2 ^ (prefixWord ++ tailWord_2721770).sum := by decide
  have hdescent : baseEnd_2721770 < baseStart_2721770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721843 : List Nat := [1, 1, 1, 2, 4, 1, 2, 10]
def baseStart_2721843 : Nat := 118140960795 + 2721843 * 2 ^ 59
def prefixEnd_2721843 : Nat := 4983230072969 + 3 ^ 40 * 2721843 * 2
def baseEnd_2721843 : Nat := 103526942598199963736665

theorem tailTrace_2721843 : CollatzResearch.WordTrace tailWord_2721843 prefixEnd_2721843 103526942598199963736665 := by
  unfold tailWord_2721843
  simp only [CollatzResearch.WordTrace]
  refine ⟨99273769878235139620610183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66182513252156759747073455 99273769878235139620610183)
  ·
    refine ⟨148910654817352709430915275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99273769878235139620610183 148910654817352709430915275)
    ·
      refine ⟨223365982226029064146372913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148910654817352709430915275 223365982226029064146372913)
      ·
        refine ⟨167524486669521798109779685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223365982226029064146372913 167524486669521798109779685)
        ·
          refine ⟨31410841250535337145583691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167524486669521798109779685 31410841250535337145583691)
          ·
            refine ⟨47116261875803005718375537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31410841250535337145583691 47116261875803005718375537)
            ·
              refine ⟨35337196406852254288781653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47116261875803005718375537 35337196406852254288781653)
              ·
                refine ⟨103526942598199963736665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35337196406852254288781653 103526942598199963736665)
                ·
                  rfl

theorem cell22_2721843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 10].length) (baseStart_2721843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2721843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2721843 prefixEnd_2721843 := by exact prefixLift 2721843
  have htrace : WordTrace (prefixWord ++ tailWord_2721843) baseStart_2721843 baseEnd_2721843 := by
    simpa [prefixWord, tailWord_2721843, baseEnd_2721843] using wordTrace_append hprefix tailTrace_2721843
  have hstable : (prefixWord ++ tailWord_2721843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721843).length < 2 ^ (prefixWord ++ tailWord_2721843).sum := by decide
  have hdescent : baseEnd_2721843 < baseStart_2721843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721849 : List Nat := [1, 2, 1, 5, 3, 1, 2, 3, 4]
def baseStart_2721849 : Nat := 118140960795 + 2721849 * 2 ^ 59
def prefixEnd_2721849 : Nat := 4983230072969 + 3 ^ 40 * 2721849 * 2
def baseEnd_2721849 : Nat := 310581512435472552659989

theorem tailTrace_2721849 : CollatzResearch.WordTrace tailWord_2721849 prefixEnd_2721849 310581512435472552659989 := by
  unfold tailWord_2721849
  simp only [CollatzResearch.WordTrace]
  refine ⟨99273988716213402645328601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66182659144142268430219067 99273988716213402645328601)
  ·
    refine ⟨74455491537160051983996451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99273988716213402645328601 74455491537160051983996451)
    ·
      refine ⟨111683237305740077975994677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74455491537160051983996451 111683237305740077975994677)
      ·
        refine ⟨10470303497413132310249501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111683237305740077975994677 10470303497413132310249501)
        ·
          refine ⟨3926363811529924616343563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10470303497413132310249501 3926363811529924616343563)
          ·
            refine ⟨5889545717294886924515345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3926363811529924616343563 5889545717294886924515345)
            ·
              refine ⟨4417159287971165193386509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5889545717294886924515345 4417159287971165193386509)
              ·
                refine ⟨1656434732989186947519941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4417159287971165193386509 1656434732989186947519941)
                ·
                  refine ⟨310581512435472552659989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1656434732989186947519941 310581512435472552659989)
                  ·
                    rfl

theorem cell22_2721849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 3, 4].length) (baseStart_2721849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2721849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2721849 prefixEnd_2721849 := by exact prefixLift 2721849
  have htrace : WordTrace (prefixWord ++ tailWord_2721849) baseStart_2721849 baseEnd_2721849 := by
    simpa [prefixWord, tailWord_2721849, baseEnd_2721849] using wordTrace_append hprefix tailTrace_2721849
  have hstable : (prefixWord ++ tailWord_2721849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721849).length < 2 ^ (prefixWord ++ tailWord_2721849).sum := by decide
  have hdescent : baseEnd_2721849 < baseStart_2721849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721892 : List Nat := [2, 3, 1, 1, 2, 1, 4, 2, 3, 3]
def baseStart_2721892 : Nat := 118140960795 + 2721892 * 2 ^ 59
def prefixEnd_2721892 : Nat := 4983230072969 + 3 ^ 40 * 2721892 * 2
def baseEnd_2721892 : Nat := 931759257085179879154835

theorem tailTrace_2721892 : CollatzResearch.WordTrace tailWord_2721892 prefixEnd_2721892 931759257085179879154835 := by
  unfold tailWord_2721892
  simp only [CollatzResearch.WordTrace]
  refine ⟨49637778527528810494571965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66183704703371747326095953 49637778527528810494571965)
  ·
    refine ⟨18614166947823303935464487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49637778527528810494571965 18614166947823303935464487)
    ·
      refine ⟨27921250421734955903196731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18614166947823303935464487 27921250421734955903196731)
      ·
        refine ⟨41881875632602433854795097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27921250421734955903196731 41881875632602433854795097)
        ·
          refine ⟨31411406724451825391096323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41881875632602433854795097 31411406724451825391096323)
          ·
            refine ⟨47117110086677738086644485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31411406724451825391096323 47117110086677738086644485)
            ·
              refine ⟨8834458141252075891245841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47117110086677738086644485 8834458141252075891245841)
              ·
                refine ⟨6625843605939056918434381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8834458141252075891245841 6625843605939056918434381)
                ·
                  refine ⟨2484691352227146344412893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6625843605939056918434381 2484691352227146344412893)
                  ·
                    refine ⟨931759257085179879154835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2484691352227146344412893 931759257085179879154835)
                    ·
                      rfl

theorem cell22_2721892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_2721892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2721892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2721892 prefixEnd_2721892 := by exact prefixLift 2721892
  have htrace : WordTrace (prefixWord ++ tailWord_2721892) baseStart_2721892 baseEnd_2721892 := by
    simpa [prefixWord, tailWord_2721892, baseEnd_2721892] using wordTrace_append hprefix tailTrace_2721892
  have hstable : (prefixWord ++ tailWord_2721892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721892).length < 2 ^ (prefixWord ++ tailWord_2721892).sum := by decide
  have hdescent : baseEnd_2721892 < baseStart_2721892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721952 : List Nat := [2, 1, 1, 4, 2, 3, 1, 1, 3, 4]
def baseStart_2721952 : Nat := 118140960795 + 2721952 * 2 ^ 59
def prefixEnd_2721952 : Nat := 4983230072969 + 3 ^ 40 * 2721952 * 2
def baseEnd_2721952 : Nat := 931779796311359722654651

theorem tailTrace_2721952 : CollatzResearch.WordTrace tailWord_2721952 prefixEnd_2721952 931779796311359722654651 := by
  unfold tailWord_2721952
  simp only [CollatzResearch.WordTrace]
  refine ⟨49638872717420125618164055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66185163623226834157552073 49638872717420125618164055)
  ·
    refine ⟨74458309076130188427246083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49638872717420125618164055 74458309076130188427246083)
    ·
      refine ⟨111687463614195282640869125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74458309076130188427246083 111687463614195282640869125)
      ·
        refine ⟨20941399427661615495162961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111687463614195282640869125 20941399427661615495162961)
        ·
          refine ⟨15706049570746211621372221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20941399427661615495162961 15706049570746211621372221)
          ·
            refine ⟨5889768589029829358014583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15706049570746211621372221 5889768589029829358014583)
            ·
              refine ⟨8834652883544744037021875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5889768589029829358014583 8834652883544744037021875)
              ·
                refine ⟨13251979325317116055532813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8834652883544744037021875 13251979325317116055532813)
                ·
                  refine ⟨4969492246993918520824805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13251979325317116055532813 4969492246993918520824805)
                  ·
                    refine ⟨931779796311359722654651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4969492246993918520824805 931779796311359722654651)
                    ·
                      rfl

theorem cell22_2721952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 3, 4].length) (baseStart_2721952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2721952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2721952 prefixEnd_2721952 := by exact prefixLift 2721952
  have htrace : WordTrace (prefixWord ++ tailWord_2721952) baseStart_2721952 baseEnd_2721952 := by
    simpa [prefixWord, tailWord_2721952, baseEnd_2721952] using wordTrace_append hprefix tailTrace_2721952
  have hstable : (prefixWord ++ tailWord_2721952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721952).length < 2 ^ (prefixWord ++ tailWord_2721952).sum := by decide
  have hdescent : baseEnd_2721952 < baseStart_2721952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721967 : List Nat := [1, 1, 2, 1, 2, 3, 1, 7, 4]
def baseStart_2721967 : Nat := 118140960795 + 2721967 * 2 ^ 59
def prefixEnd_2721967 : Nat := 4983230072969 + 3 ^ 40 * 2721967 * 2
def baseEnd_2721967 : Nat := 310594977039301561176535

theorem tailTrace_2721967 : CollatzResearch.WordTrace tailWord_2721967 prefixEnd_2721967 310594977039301561176535 := by
  unfold tailWord_2721967
  simp only [CollatzResearch.WordTrace]
  refine ⟨99278292529785908798124155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66185528353190605865416103 99278292529785908798124155)
  ·
    refine ⟨148917438794678863197186233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99278292529785908798124155 148917438794678863197186233)
    ·
      refine ⟨111688079096009147397889675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148917438794678863197186233 111688079096009147397889675)
      ·
        refine ⟨167532118644013721096834513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111688079096009147397889675 167532118644013721096834513)
        ·
          refine ⟨125649088983010290822625885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167532118644013721096834513 125649088983010290822625885)
          ·
            refine ⟨47118408368628859058484707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125649088983010290822625885 47118408368628859058484707)
            ·
              refine ⟨70677612552943288587727061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47118408368628859058484707 70677612552943288587727061)
              ·
                refine ⟨1656506544209608326274853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 70677612552943288587727061 1656506544209608326274853)
                ·
                  refine ⟨310594977039301561176535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1656506544209608326274853 310594977039301561176535)
                  ·
                    rfl

theorem cell22_2721967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 7, 4].length) (baseStart_2721967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2721967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2721967 prefixEnd_2721967 := by exact prefixLift 2721967
  have htrace : WordTrace (prefixWord ++ tailWord_2721967) baseStart_2721967 baseEnd_2721967 := by
    simpa [prefixWord, tailWord_2721967, baseEnd_2721967] using wordTrace_append hprefix tailTrace_2721967
  have hstable : (prefixWord ++ tailWord_2721967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721967).length < 2 ^ (prefixWord ++ tailWord_2721967).sum := by decide
  have hdescent : baseEnd_2721967 < baseStart_2721967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721984 : List Nat := [2, 1, 1, 2, 5, 2, 1, 4, 4]
def baseStart_2721984 : Nat := 118140960795 + 2721984 * 2 ^ 59
def prefixEnd_2721984 : Nat := 4983230072969 + 3 ^ 40 * 2721984 * 2
def baseEnd_2721984 : Nat := 310596916855107435284851

theorem tailTrace_2721984 : CollatzResearch.WordTrace tailWord_2721984 prefixEnd_2721984 310596916855107435284851 := by
  unfold tailWord_2721984
  simp only [CollatzResearch.WordTrace]
  refine ⟨49639456285362160350746503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66185941713816213800995337 49639456285362160350746503)
  ·
    refine ⟨74459184428043240526119755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49639456285362160350746503 74459184428043240526119755)
    ·
      refine ⟨111688776642064860789179633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74459184428043240526119755 111688776642064860789179633)
      ·
        refine ⟨83766582481548645591884725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111688776642064860789179633 83766582481548645591884725)
        ·
          refine ⟨7853117107645185524239193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83766582481548645591884725 7853117107645185524239193)
          ·
            refine ⟨5889837830733889143179395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7853117107645185524239193 5889837830733889143179395)
            ·
              refine ⟨8834756746100833714769093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5889837830733889143179395 8834756746100833714769093)
              ·
                refine ⟨1656516889893906321519205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8834756746100833714769093 1656516889893906321519205)
                ·
                  refine ⟨310596916855107435284851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1656516889893906321519205 310596916855107435284851)
                  ·
                    rfl

theorem cell22_2721984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 4, 4].length) (baseStart_2721984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2721984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2721984 prefixEnd_2721984 := by exact prefixLift 2721984
  have htrace : WordTrace (prefixWord ++ tailWord_2721984) baseStart_2721984 baseEnd_2721984 := by
    simpa [prefixWord, tailWord_2721984, baseEnd_2721984] using wordTrace_append hprefix tailTrace_2721984
  have hstable : (prefixWord ++ tailWord_2721984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721984).length < 2 ^ (prefixWord ++ tailWord_2721984).sum := by decide
  have hdescent : baseEnd_2721984 < baseStart_2721984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721986 : List Nat := [3, 5, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_2721986 : Nat := 118140960795 + 2721986 * 2 ^ 59
def prefixEnd_2721986 : Nat := 4983230072969 + 3 ^ 40 * 2721986 * 2
def baseEnd_2721986 : Nat := 931791435206194967304547

theorem tailTrace_2721986 : CollatzResearch.WordTrace tailWord_2721986 prefixEnd_2721986 931791435206194967304547 := by
  unfold tailWord_2721986
  simp only [CollatzResearch.WordTrace]
  refine ⟨24819746379179268760766453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66185990344478050028710541 24819746379179268760766453)
  ·
    refine ⟨2326851223048056446321855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24819746379179268760766453 2326851223048056446321855)
    ·
      refine ⟨3490276834572084669482783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2326851223048056446321855 3490276834572084669482783)
      ·
        refine ⟨5235415251858127004224175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3490276834572084669482783 5235415251858127004224175)
        ·
          refine ⟨7853122877787190506336263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5235415251858127004224175 7853122877787190506336263)
          ·
            refine ⟨11779684316680785759504395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7853122877787190506336263 11779684316680785759504395)
            ·
              refine ⟨17669526475021178639256593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11779684316680785759504395 17669526475021178639256593)
              ·
                refine ⟨13252144856265883979442445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17669526475021178639256593 13252144856265883979442445)
                ·
                  refine ⟨4969554321099706492290917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13252144856265883979442445 4969554321099706492290917)
                  ·
                    refine ⟨931791435206194967304547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4969554321099706492290917 931791435206194967304547)
                    ·
                      rfl

theorem cell22_2721986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_2721986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2721986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2721986 prefixEnd_2721986 := by exact prefixLift 2721986
  have htrace : WordTrace (prefixWord ++ tailWord_2721986) baseStart_2721986 baseEnd_2721986 := by
    simpa [prefixWord, tailWord_2721986, baseEnd_2721986] using wordTrace_append hprefix tailTrace_2721986
  have hstable : (prefixWord ++ tailWord_2721986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721986).length < 2 ^ (prefixWord ++ tailWord_2721986).sum := by decide
  have hdescent : baseEnd_2721986 < baseStart_2721986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722025 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 4, 6]
def baseStart_2722025 : Nat := 118140960795 + 2722025 * 2 ^ 59
def prefixEnd_2722025 : Nat := 4983230072969 + 3 ^ 40 * 2722025 * 2
def baseEnd_2722025 : Nat := 931804785703211865579427

theorem tailTrace_2722025 : CollatzResearch.WordTrace tailWord_2722025 prefixEnd_2722025 931804785703211865579427 := by
  unfold tailWord_2722025
  simp only [CollatzResearch.WordTrace]
  refine ⟨99280407963575784703735529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66186938642383856469157019 99280407963575784703735529)
  ·
    refine ⟨74460305972681838527801647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99280407963575784703735529 74460305972681838527801647)
    ·
      refine ⟨111690458959022757791702471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74460305972681838527801647 111690458959022757791702471)
      ·
        refine ⟨167535688438534136687553707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111690458959022757791702471 167535688438534136687553707)
        ·
          refine ⟨251303532657801205031330561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167535688438534136687553707 251303532657801205031330561)
          ·
            refine ⟨188477649493350903773497921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251303532657801205031330561 188477649493350903773497921)
            ·
              refine ⟨141358237120013177830123441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188477649493350903773497921 141358237120013177830123441)
              ·
                refine ⟨106018677840009883372592581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141358237120013177830123441 106018677840009883372592581)
                ·
                  refine ⟨19878502095001853132361109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106018677840009883372592581 19878502095001853132361109)
                  ·
                    refine ⟨931804785703211865579427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19878502095001853132361109 931804785703211865579427)
                    ·
                      rfl

theorem cell22_2722025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 6].length) (baseStart_2722025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2722025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2722025 prefixEnd_2722025 := by exact prefixLift 2722025
  have htrace : WordTrace (prefixWord ++ tailWord_2722025) baseStart_2722025 baseEnd_2722025 := by
    simpa [prefixWord, tailWord_2722025, baseEnd_2722025] using wordTrace_append hprefix tailTrace_2722025
  have hstable : (prefixWord ++ tailWord_2722025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722025).length < 2 ^ (prefixWord ++ tailWord_2722025).sum := by decide
  have hdescent : baseEnd_2722025 < baseStart_2722025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722027 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 5, 3]
def baseStart_2722027 : Nat := 118140960795 + 2722027 * 2 ^ 59
def prefixEnd_2722027 : Nat := 4983230072969 + 3 ^ 40 * 2722027 * 2
def baseEnd_2722027 : Nat := 931805470344084527029421

theorem tailTrace_2722027 : CollatzResearch.WordTrace tailWord_2722027 prefixEnd_2722027 931805470344084527029421 := by
  unfold tailWord_2722027
  simp only [CollatzResearch.WordTrace]
  refine ⟨99280480909568539045308335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66186987273045692696872223 99280480909568539045308335)
  ·
    refine ⟨148920721364352808567962503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99280480909568539045308335 148920721364352808567962503)
    ·
      refine ⟨223381082046529212851943755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148920721364352808567962503 223381082046529212851943755)
      ·
        refine ⟨335071623069793819277915633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223381082046529212851943755 335071623069793819277915633)
        ·
          refine ⟨251303717302345364458436725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335071623069793819277915633 251303717302345364458436725)
          ·
            refine ⟨23559723497094877917978443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 251303717302345364458436725 23559723497094877917978443)
            ·
              refine ⟨35339585245642316876967665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23559723497094877917978443 35339585245642316876967665)
              ·
                refine ⟨26504688934231737657725749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35339585245642316876967665 26504688934231737657725749)
                ·
                  refine ⟨2484814587584225405411789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26504688934231737657725749 2484814587584225405411789)
                  ·
                    refine ⟨931805470344084527029421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2484814587584225405411789 931805470344084527029421)
                    ·
                      rfl

theorem cell22_2722027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 5, 3].length) (baseStart_2722027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2722027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2722027 prefixEnd_2722027 := by exact prefixLift 2722027
  have htrace : WordTrace (prefixWord ++ tailWord_2722027) baseStart_2722027 baseEnd_2722027 := by
    simpa [prefixWord, tailWord_2722027, baseEnd_2722027] using wordTrace_append hprefix tailTrace_2722027
  have hstable : (prefixWord ++ tailWord_2722027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722027).length < 2 ^ (prefixWord ++ tailWord_2722027).sum := by decide
  have hdescent : baseEnd_2722027 < baseStart_2722027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722044 : List Nat := [2, 2, 2, 1, 4, 1, 1, 3, 3, 3]
def baseStart_2722044 : Nat := 118140960795 + 2722044 * 2 ^ 59
def prefixEnd_2722044 : Nat := 4983230072969 + 3 ^ 40 * 2722044 * 2
def baseEnd_2722044 : Nat := 931811289791502149354369

theorem tailTrace_2722044 : CollatzResearch.WordTrace tailWord_2722044 prefixEnd_2722044 931811289791502149354369 := by
  unfold tailWord_2722044
  simp only [CollatzResearch.WordTrace]
  refine ⟨49640550475253475474338593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66187400633671300632451457 49640550475253475474338593)
  ·
    refine ⟨37230412856440106605753945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49640550475253475474338593 37230412856440106605753945)
    ·
      refine ⟨27922809642330079954315459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37230412856440106605753945 27922809642330079954315459)
      ·
        refine ⟨41884214463495119931473189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27922809642330079954315459 41884214463495119931473189)
        ·
          refine ⟨7853290211905334987151223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41884214463495119931473189 7853290211905334987151223)
          ·
            refine ⟨11779935317858002480726835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7853290211905334987151223 11779935317858002480726835)
            ·
              refine ⟨17669902976787003721090253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11779935317858002480726835 17669902976787003721090253)
              ·
                refine ⟨6626213616295126395408845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17669902976787003721090253 6626213616295126395408845)
                ·
                  refine ⟨2484830106110672398278317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6626213616295126395408845 2484830106110672398278317)
                  ·
                    refine ⟨931811289791502149354369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2484830106110672398278317 931811289791502149354369)
                    ·
                      rfl

theorem cell22_2722044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_2722044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2722044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2722044 prefixEnd_2722044 := by exact prefixLift 2722044
  have htrace : WordTrace (prefixWord ++ tailWord_2722044) baseStart_2722044 baseEnd_2722044 := by
    simpa [prefixWord, tailWord_2722044, baseEnd_2722044] using wordTrace_append hprefix tailTrace_2722044
  have hstable : (prefixWord ++ tailWord_2722044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722044).length < 2 ^ (prefixWord ++ tailWord_2722044).sum := by decide
  have hdescent : baseEnd_2722044 < baseStart_2722044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722142 : List Nat := [4, 4, 2, 1, 1, 1, 2, 2, 5]
def baseStart_2722142 : Nat := 118140960795 + 2722142 * 2 ^ 59
def prefixEnd_2722142 : Nat := 4983230072969 + 3 ^ 40 * 2722142 * 2
def baseEnd_2722142 : Nat := 310614945731420853468023

theorem tailTrace_2722142 : CollatzResearch.WordTrace tailWord_2722142 prefixEnd_2722142 310614945731420853468023 := by
  unfold tailWord_2722142
  simp only [CollatzResearch.WordTrace]
  refine ⟨12410584413018989210718085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66189783536101275790496453 12410584413018989210718085)
  ·
    refine ⟨2326984577441060477009641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12410584413018989210718085 2326984577441060477009641)
    ·
      refine ⟨1745238433080795357757231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2326984577441060477009641 1745238433080795357757231)
      ·
        refine ⟨2617857649621193036635847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1745238433080795357757231 2617857649621193036635847)
        ·
          refine ⟨3926786474431789554953771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2617857649621193036635847 3926786474431789554953771)
          ·
            refine ⟨5890179711647684332430657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3926786474431789554953771 5890179711647684332430657)
            ·
              refine ⟨4417634783735763249322993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5890179711647684332430657 4417634783735763249322993)
              ·
                refine ⟨3313226087801822436992245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4417634783735763249322993 3313226087801822436992245)
                ·
                  refine ⟨310614945731420853468023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3313226087801822436992245 310614945731420853468023)
                  ·
                    rfl

theorem cell22_2722142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_2722142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2722142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2722142 prefixEnd_2722142 := by exact prefixLift 2722142
  have htrace : WordTrace (prefixWord ++ tailWord_2722142) baseStart_2722142 baseEnd_2722142 := by
    simpa [prefixWord, tailWord_2722142, baseEnd_2722142] using wordTrace_append hprefix tailTrace_2722142
  have hstable : (prefixWord ++ tailWord_2722142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722142).length < 2 ^ (prefixWord ++ tailWord_2722142).sum := by decide
  have hdescent : baseEnd_2722142 < baseStart_2722142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722149 : List Nat := [1, 3, 1, 3, 1, 3, 2, 2, 2, 4]
def baseStart_2722149 : Nat := 118140960795 + 2722149 * 2 ^ 59
def prefixEnd_2722149 : Nat := 4983230072969 + 3 ^ 40 * 2722149 * 2
def baseEnd_2722149 : Nat := 931847233437316875479047

theorem tailTrace_2722149 : CollatzResearch.WordTrace tailWord_2722149 prefixEnd_2722149 931847233437316875479047 := by
  unfold tailWord_2722149
  simp only [CollatzResearch.WordTrace]
  refine ⟨99284930615126553881249501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66189953743417702587499667 99284930615126553881249501)
  ·
    refine ⟨37231848980672457705468563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99284930615126553881249501 37231848980672457705468563)
    ·
      refine ⟨55847773471008686558202845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37231848980672457705468563 55847773471008686558202845)
      ·
        refine ⟨20942915051628257459326067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55847773471008686558202845 20942915051628257459326067)
        ·
          refine ⟨31414372577442386188989101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20942915051628257459326067 31414372577442386188989101)
          ·
            refine ⟨11780389716540894820870913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31414372577442386188989101 11780389716540894820870913)
            ·
              refine ⟨8835292287405671115653185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11780389716540894820870913 8835292287405671115653185)
              ·
                refine ⟨6626469215554253336739889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8835292287405671115653185 6626469215554253336739889)
                ·
                  refine ⟨4969851911665690002554917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6626469215554253336739889 4969851911665690002554917)
                  ·
                    refine ⟨931847233437316875479047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4969851911665690002554917 931847233437316875479047)
                    ·
                      rfl

theorem cell22_2722149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_2722149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2722149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2722149 prefixEnd_2722149 := by exact prefixLift 2722149
  have htrace : WordTrace (prefixWord ++ tailWord_2722149) baseStart_2722149 baseEnd_2722149 := by
    simpa [prefixWord, tailWord_2722149, baseEnd_2722149] using wordTrace_append hprefix tailTrace_2722149
  have hstable : (prefixWord ++ tailWord_2722149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722149).length < 2 ^ (prefixWord ++ tailWord_2722149).sum := by decide
  have hdescent : baseEnd_2722149 < baseStart_2722149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722151 : List Nat := [1, 1, 5, 1, 3, 1, 1, 4, 2, 3]
def baseStart_2722151 : Nat := 118140960795 + 2722151 * 2 ^ 59
def prefixEnd_2722151 : Nat := 4983230072969 + 3 ^ 40 * 2722151 * 2
def baseEnd_2722151 : Nat := 931847918078189536929041

theorem tailTrace_2722151 : CollatzResearch.WordTrace tailWord_2722151 prefixEnd_2722151 931847918078189536929041 := by
  unfold tailWord_2722151
  simp only [CollatzResearch.WordTrace]
  refine ⟨99285003561119308222822307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66190002374079538815214871 99285003561119308222822307)
  ·
    refine ⟨148927505341678962334233461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99285003561119308222822307 148927505341678962334233461)
    ·
      refine ⟨13961953625782402718834387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 148927505341678962334233461 13961953625782402718834387)
      ·
        refine ⟨20942930438673604078251581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13961953625782402718834387 20942930438673604078251581)
        ·
          refine ⟨7853598914502601529344343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20942930438673604078251581 7853598914502601529344343)
          ·
            refine ⟨11780398371753902294016515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7853598914502601529344343 11780398371753902294016515)
            ·
              refine ⟨17670597557630853441024773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11780398371753902294016515 17670597557630853441024773)
              ·
                refine ⟨3313237042055785020192145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17670597557630853441024773 3313237042055785020192145)
                ·
                  refine ⟨2484927781541838765144109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3313237042055785020192145 2484927781541838765144109)
                  ·
                    refine ⟨931847918078189536929041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2484927781541838765144109 931847918078189536929041)
                    ·
                      rfl

theorem cell22_2722151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_2722151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2722151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2722151 prefixEnd_2722151 := by exact prefixLift 2722151
  have htrace : WordTrace (prefixWord ++ tailWord_2722151) baseStart_2722151 baseEnd_2722151 := by
    simpa [prefixWord, tailWord_2722151, baseEnd_2722151] using wordTrace_append hprefix tailTrace_2722151
  have hstable : (prefixWord ++ tailWord_2722151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722151).length < 2 ^ (prefixWord ++ tailWord_2722151).sum := by decide
  have hdescent : baseEnd_2722151 < baseStart_2722151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722226 : List Nat := [3, 2, 1, 1, 1, 1, 7, 1, 5]
def baseStart_2722226 : Nat := 118140960795 + 2722226 * 2 ^ 59
def prefixEnd_2722226 : Nat := 4983230072969 + 3 ^ 40 * 2722226 * 2
def baseEnd_2722226 : Nat := 310624530703638113767937

theorem tailTrace_2722226 : CollatzResearch.WordTrace tailWord_2722226 prefixEnd_2722226 310624530703638113767937 := by
  unfold tailWord_2722226
  simp only [CollatzResearch.WordTrace]
  refine ⟨24821934758961899007950633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66191826023898397354535021 24821934758961899007950633)
  ·
    refine ⟨18616451069221424255962975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24821934758961899007950633 18616451069221424255962975)
    ·
      refine ⟨27924676603832136383944463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18616451069221424255962975 27924676603832136383944463)
      ·
        refine ⟨41887014905748204575916695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27924676603832136383944463 41887014905748204575916695)
        ·
          refine ⟨62830522358622306863875043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41887014905748204575916695 62830522358622306863875043)
          ·
            refine ⟨94245783537933460295812565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62830522358622306863875043 94245783537933460295812565)
            ·
              refine ⟨2208885551670315475683107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 94245783537933460295812565 2208885551670315475683107)
              ·
                refine ⟨3313328327505473213524661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2208885551670315475683107 3313328327505473213524661)
                ·
                  refine ⟨310624530703638113767937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3313328327505473213524661 310624530703638113767937)
                  ·
                    rfl

theorem cell22_2722226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_2722226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2722226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2722226 prefixEnd_2722226 := by exact prefixLift 2722226
  have htrace : WordTrace (prefixWord ++ tailWord_2722226) baseStart_2722226 baseEnd_2722226 := by
    simpa [prefixWord, tailWord_2722226, baseEnd_2722226] using wordTrace_append hprefix tailTrace_2722226
  have hstable : (prefixWord ++ tailWord_2722226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722226).length < 2 ^ (prefixWord ++ tailWord_2722226).sum := by decide
  have hdescent : baseEnd_2722226 < baseStart_2722226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722271 : List Nat := [1, 1, 2, 3, 3, 4, 1, 1, 6]
def baseStart_2722271 : Nat := 118140960795 + 2722271 * 2 ^ 59
def prefixEnd_2722271 : Nat := 4983230072969 + 3 ^ 40 * 2722271 * 2
def baseEnd_2722271 : Nat := 310629665510183074642891

theorem tailTrace_2722271 : CollatzResearch.WordTrace tailWord_2722271 prefixEnd_2722271 310629665510183074642891 := by
  unfold tailWord_2722271
  simp only [CollatzResearch.WordTrace]
  refine ⟨99289380320684568717190667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66192920213789712478127111 99289380320684568717190667)
  ·
    refine ⟨148934070481026853075786001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99289380320684568717190667 148934070481026853075786001)
    ·
      refine ⟨111700552860770139806839501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148934070481026853075786001 111700552860770139806839501)
      ·
        refine ⟨41887707322788802427564813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111700552860770139806839501 41887707322788802427564813)
        ·
          refine ⟨15707890246045800910336805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41887707322788802427564813 15707890246045800910336805)
          ·
            refine ⟨2945229421133587670688151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15707890246045800910336805 2945229421133587670688151)
            ·
              refine ⟨4417844131700381506032227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2945229421133587670688151 4417844131700381506032227)
              ·
                refine ⟨6626766197550572259048341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4417844131700381506032227 6626766197550572259048341)
                ·
                  refine ⟨310629665510183074642891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6626766197550572259048341 310629665510183074642891)
                  ·
                    rfl

theorem cell22_2722271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 6].length) (baseStart_2722271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2722271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2722271 prefixEnd_2722271 := by exact prefixLift 2722271
  have htrace : WordTrace (prefixWord ++ tailWord_2722271) baseStart_2722271 baseEnd_2722271 := by
    simpa [prefixWord, tailWord_2722271, baseEnd_2722271] using wordTrace_append hprefix tailTrace_2722271
  have hstable : (prefixWord ++ tailWord_2722271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722271).length < 2 ^ (prefixWord ++ tailWord_2722271).sum := by decide
  have hdescent : baseEnd_2722271 < baseStart_2722271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722284 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 4, 4]
def baseStart_2722284 : Nat := 118140960795 + 2722284 * 2 ^ 59
def prefixEnd_2722284 : Nat := 4983230072969 + 3 ^ 40 * 2722284 * 2
def baseEnd_2722284 : Nat := 931893446696221523353633

theorem tailTrace_2722284 : CollatzResearch.WordTrace tailWord_2722284 prefixEnd_2722284 931893446696221523353633 := by
  unfold tailWord_2722284
  simp only [CollatzResearch.WordTrace]
  refine ⟨49644927234818735968706953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66193236313091647958275937 49644927234818735968706953)
  ·
    refine ⟨37233695426114051976530215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49644927234818735968706953 37233695426114051976530215)
    ·
      refine ⟨55850543139171077964795323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37233695426114051976530215 55850543139171077964795323)
      ·
        refine ⟨83775814708756616947192985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55850543139171077964795323 83775814708756616947192985)
        ·
          refine ⟨62831861031567462710394739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83775814708756616947192985 62831861031567462710394739)
          ·
            refine ⟨94247791547351194065592109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62831861031567462710394739 94247791547351194065592109)
            ·
              refine ⟨35342921830256697774597041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94247791547351194065592109 35342921830256697774597041)
              ·
                refine ⟨26507191372692523330947781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35342921830256697774597041 26507191372692523330947781)
                ·
                  refine ⟨4970098382379848124552709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26507191372692523330947781 4970098382379848124552709)
                  ·
                    refine ⟨931893446696221523353633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4970098382379848124552709 931893446696221523353633)
                    ·
                      rfl

theorem cell22_2722284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_2722284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2722284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2722284 prefixEnd_2722284 := by exact prefixLift 2722284
  have htrace : WordTrace (prefixWord ++ tailWord_2722284) baseStart_2722284 baseEnd_2722284 := by
    simpa [prefixWord, tailWord_2722284, baseEnd_2722284] using wordTrace_append hprefix tailTrace_2722284
  have hstable : (prefixWord ++ tailWord_2722284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722284).length < 2 ^ (prefixWord ++ tailWord_2722284).sum := by decide
  have hdescent : baseEnd_2722284 < baseStart_2722284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722290 : List Nat := [3, 2, 1, 4, 2, 2, 1, 2, 1, 4]
def baseStart_2722290 : Nat := 118140960795 + 2722290 * 2 ^ 59
def prefixEnd_2722290 : Nat := 4983230072969 + 3 ^ 40 * 2722290 * 2
def baseEnd_2722290 : Nat := 931895500618839507703615

theorem tailTrace_2722290 : CollatzResearch.WordTrace tailWord_2722290 prefixEnd_2722290 931895500618839507703615 := by
  unfold tailWord_2722290
  simp only [CollatzResearch.WordTrace]
  refine ⟨24822518326903933740533081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66193382205077156641421549 24822518326903933740533081)
  ·
    refine ⟨18616888745177950305399811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24822518326903933740533081 18616888745177950305399811)
    ·
      refine ⟨27925333117766925458099717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18616888745177950305399811 27925333117766925458099717)
      ·
        refine ⟨5235999959581298523393697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27925333117766925458099717 5235999959581298523393697)
        ·
          refine ⟨3926999969685973892545273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5235999959581298523393697 3926999969685973892545273)
          ·
            refine ⟨2945249977264480419408955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3926999969685973892545273 2945249977264480419408955)
            ·
              refine ⟨4417874965896720629113433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2945249977264480419408955 4417874965896720629113433)
              ·
                refine ⟨3313406224422540471835075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4417874965896720629113433 3313406224422540471835075)
                ·
                  refine ⟨4970109336633810707752613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3313406224422540471835075 4970109336633810707752613)
                  ·
                    refine ⟨931895500618839507703615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4970109336633810707752613 931895500618839507703615)
                    ·
                      rfl

theorem cell22_2722290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_2722290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2722290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2722290 prefixEnd_2722290 := by exact prefixLift 2722290
  have htrace : WordTrace (prefixWord ++ tailWord_2722290) baseStart_2722290 baseEnd_2722290 := by
    simpa [prefixWord, tailWord_2722290, baseEnd_2722290] using wordTrace_append hprefix tailTrace_2722290
  have hstable : (prefixWord ++ tailWord_2722290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722290).length < 2 ^ (prefixWord ++ tailWord_2722290).sum := by decide
  have hdescent : baseEnd_2722290 < baseStart_2722290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722301 : List Nat := [1, 4, 1, 1, 1, 3, 4, 1, 2, 4]
def baseStart_2722301 : Nat := 118140960795 + 2722301 * 2 ^ 59
def prefixEnd_2722301 : Nat := 4983230072969 + 3 ^ 40 * 2722301 * 2
def baseEnd_2722301 : Nat := 931899266143639145678581

theorem tailTrace_2722301 : CollatzResearch.WordTrace tailWord_2722301 prefixEnd_2722301 931899266143639145678581 := by
  unfold tailWord_2722301
  simp only [CollatzResearch.WordTrace]
  refine ⟨99290474510575883840782757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66193649673717255893855171 99290474510575883840782757)
  ·
    refine ⟨18616963970732978220146767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99290474510575883840782757 18616963970732978220146767)
    ·
      refine ⟨27925445956099467330220151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18616963970732978220146767 27925445956099467330220151)
      ·
        refine ⟨41888168934149200995330227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27925445956099467330220151 41888168934149200995330227)
        ·
          refine ⟨62832253401223801492995341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41888168934149200995330227 62832253401223801492995341)
          ·
            refine ⟨23562095025458925559873253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62832253401223801492995341 23562095025458925559873253)
            ·
              refine ⟨4417892817273548542476235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23562095025458925559873253 4417892817273548542476235)
              ·
                refine ⟨6626839225910322813714353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4417892817273548542476235 6626839225910322813714353)
                ·
                  refine ⟨4970129419432742110285765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6626839225910322813714353 4970129419432742110285765)
                  ·
                    refine ⟨931899266143639145678581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4970129419432742110285765 931899266143639145678581)
                    ·
                      rfl

theorem cell22_2722301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_2722301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2722301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2722301 prefixEnd_2722301 := by exact prefixLift 2722301
  have htrace : WordTrace (prefixWord ++ tailWord_2722301) baseStart_2722301 baseEnd_2722301 := by
    simpa [prefixWord, tailWord_2722301, baseEnd_2722301] using wordTrace_append hprefix tailTrace_2722301
  have hstable : (prefixWord ++ tailWord_2722301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722301).length < 2 ^ (prefixWord ++ tailWord_2722301).sum := by decide
  have hdescent : baseEnd_2722301 < baseStart_2722301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722359 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 1, 7]
def baseStart_2722359 : Nat := 118140960795 + 2722359 * 2 ^ 59
def prefixEnd_2722359 : Nat := 4983230072969 + 3 ^ 40 * 2722359 * 2
def baseEnd_2722359 : Nat := 931919120728946327728403

theorem tailTrace_2722359 : CollatzResearch.WordTrace tailWord_2722359 prefixEnd_2722359 931919120728946327728403 := by
  unfold tailWord_2722359
  simp only [CollatzResearch.WordTrace]
  refine ⟨99292589944365759746394131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66195059962910506497596087 99292589944365759746394131)
  ·
    refine ⟨148938884916548639619591197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99292589944365759746394131 148938884916548639619591197)
    ·
      refine ⟨55852081843705739857346699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148938884916548639619591197 55852081843705739857346699)
      ·
        refine ⟨83778122765558609786020049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55852081843705739857346699 83778122765558609786020049)
        ·
          refine ⟨62833592074168957339515037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83778122765558609786020049 62833592074168957339515037)
          ·
            refine ⟨23562597027813359002318139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62833592074168957339515037 23562597027813359002318139)
            ·
              refine ⟨35343895541720038503477209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23562597027813359002318139 35343895541720038503477209)
              ·
                refine ⟨26507921656290028877607907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35343895541720038503477209 26507921656290028877607907)
                ·
                  refine ⟨39761882484435043316411861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26507921656290028877607907 39761882484435043316411861)
                  ·
                    refine ⟨931919120728946327728403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39761882484435043316411861 931919120728946327728403)
                    ·
                      rfl

theorem cell22_2722359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_2722359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2722359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2722359 prefixEnd_2722359 := by exact prefixLift 2722359
  have htrace : WordTrace (prefixWord ++ tailWord_2722359) baseStart_2722359 baseEnd_2722359 := by
    simpa [prefixWord, tailWord_2722359, baseEnd_2722359] using wordTrace_append hprefix tailTrace_2722359
  have hstable : (prefixWord ++ tailWord_2722359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722359).length < 2 ^ (prefixWord ++ tailWord_2722359).sum := by decide
  have hdescent : baseEnd_2722359 < baseStart_2722359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722365 : List Nat := [1, 4, 1, 3, 2, 1, 1, 5, 1, 3]
def baseStart_2722365 : Nat := 118140960795 + 2722365 * 2 ^ 59
def prefixEnd_2722365 : Nat := 4983230072969 + 3 ^ 40 * 2722365 * 2
def baseEnd_2722365 : Nat := 931921174651564312078385

theorem tailTrace_2722365 : CollatzResearch.WordTrace tailWord_2722365 prefixEnd_2722365 931921174651564312078385 := by
  unfold tailWord_2722365
  simp only [CollatzResearch.WordTrace]
  refine ⟨99292808782344022771112549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66195205854896015180741699 99292808782344022771112549)
  ·
    refine ⟨18617401646689504269583603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99292808782344022771112549 18617401646689504269583603)
    ·
      refine ⟨27926102470034256404375405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18617401646689504269583603 27926102470034256404375405)
      ·
        refine ⟨10472288426262846151640777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27926102470034256404375405 10472288426262846151640777)
        ·
          refine ⟨7854216319697134613730583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10472288426262846151640777 7854216319697134613730583)
          ·
            refine ⟨11781324479545701920595875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7854216319697134613730583 11781324479545701920595875)
            ·
              refine ⟨17671986719318552880893813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11781324479545701920595875 17671986719318552880893813)
              ·
                refine ⟨1656748754936114332583795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17671986719318552880893813 1656748754936114332583795)
                ·
                  refine ⟨2485123132404171498875693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1656748754936114332583795 2485123132404171498875693)
                  ·
                    refine ⟨931921174651564312078385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2485123132404171498875693 931921174651564312078385)
                    ·
                      rfl

theorem cell22_2722365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_2722365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2722365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2722365 prefixEnd_2722365 := by exact prefixLift 2722365
  have htrace : WordTrace (prefixWord ++ tailWord_2722365) baseStart_2722365 baseEnd_2722365 := by
    simpa [prefixWord, tailWord_2722365, baseEnd_2722365] using wordTrace_append hprefix tailTrace_2722365
  have hstable : (prefixWord ++ tailWord_2722365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722365).length < 2 ^ (prefixWord ++ tailWord_2722365).sum := by decide
  have hdescent : baseEnd_2722365 < baseStart_2722365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722378 : List Nat := [3, 1, 2, 1, 1, 6, 1, 2, 5]
def baseStart_2722378 : Nat := 118140960795 + 2722378 * 2 ^ 59
def prefixEnd_2722378 : Nat := 4983230072969 + 3 ^ 40 * 2722378 * 2
def baseEnd_2722378 : Nat := 310641874939078870501115

theorem tailTrace_2722378 : CollatzResearch.WordTrace tailWord_2722378 prefixEnd_2722378 310641874939078870501115 := by
  unfold tailWord_2722378
  simp only [CollatzResearch.WordTrace]
  refine ⟨24823320732824231497833947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66195521954197950660890525 24823320732824231497833947)
  ·
    refine ⟨37234981099236347246750921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24823320732824231497833947 37234981099236347246750921)
    ·
      refine ⟨27926235824427260435063191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37234981099236347246750921 27926235824427260435063191)
      ·
        refine ⟨41889353736640890652594787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27926235824427260435063191 41889353736640890652594787)
        ·
          refine ⟨62834030604961335978892181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41889353736640890652594787 62834030604961335978892181)
          ·
            refine ⟨2945345184607562624010571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62834030604961335978892181 2945345184607562624010571)
            ·
              refine ⟨4418017776911343936015857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2945345184607562624010571 4418017776911343936015857)
              ·
                refine ⟨3313513332683507952011893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4418017776911343936015857 3313513332683507952011893)
                ·
                  refine ⟨310641874939078870501115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3313513332683507952011893 310641874939078870501115)
                  ·
                    rfl

theorem cell22_2722378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 5].length) (baseStart_2722378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2722378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2722378 prefixEnd_2722378 := by exact prefixLift 2722378
  have htrace : WordTrace (prefixWord ++ tailWord_2722378) baseStart_2722378 baseEnd_2722378 := by
    simpa [prefixWord, tailWord_2722378, baseEnd_2722378] using wordTrace_append hprefix tailTrace_2722378
  have hstable : (prefixWord ++ tailWord_2722378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722378).length < 2 ^ (prefixWord ++ tailWord_2722378).sum := by decide
  have hdescent : baseEnd_2722378 < baseStart_2722378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722423 : List Nat := [1, 1, 3, 1, 1, 3, 5, 3, 4]
def baseStart_2722423 : Nat := 118140960795 + 2722423 * 2 ^ 59
def prefixEnd_2722423 : Nat := 4983230072969 + 3 ^ 40 * 2722423 * 2
def baseEnd_2722423 : Nat := 310647009745623831376069

theorem tailTrace_2722423 : CollatzResearch.WordTrace tailWord_2722423 prefixEnd_2722423 310647009745623831376069 := by
  unfold tailWord_2722423
  simp only [CollatzResearch.WordTrace]
  refine ⟨99294924216133898676723923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66196616144089265784482615 99294924216133898676723923)
  ·
    refine ⟨148942386324200848015085885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99294924216133898676723923 148942386324200848015085885)
    ·
      refine ⟨55853394871575318005657207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148942386324200848015085885 55853394871575318005657207)
      ·
        refine ⟨83780092307362977008485811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55853394871575318005657207 83780092307362977008485811)
        ·
          refine ⟨125670138461044465512728717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83780092307362977008485811 125670138461044465512728717)
          ·
            refine ⟨47126301922891674567273269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125670138461044465512728717 47126301922891674567273269)
            ·
              refine ⟨4418090805271094490681869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47126301922891674567273269 4418090805271094490681869)
              ·
                refine ⟨1656784051976660434005701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4418090805271094490681869 1656784051976660434005701)
                ·
                  refine ⟨310647009745623831376069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1656784051976660434005701 310647009745623831376069)
                  ·
                    rfl

theorem cell22_2722423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 3, 4].length) (baseStart_2722423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2722423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2722423 prefixEnd_2722423 := by exact prefixLift 2722423
  have htrace : WordTrace (prefixWord ++ tailWord_2722423) baseStart_2722423 baseEnd_2722423 := by
    simpa [prefixWord, tailWord_2722423, baseEnd_2722423] using wordTrace_append hprefix tailTrace_2722423
  have hstable : (prefixWord ++ tailWord_2722423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722423).length < 2 ^ (prefixWord ++ tailWord_2722423).sum := by decide
  have hdescent : baseEnd_2722423 < baseStart_2722423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722517 : List Nat := [1, 3, 2, 5, 1, 1, 1, 2, 3, 3]
def baseStart_2722517 : Nat := 118140960795 + 2722517 * 2 ^ 59
def prefixEnd_2722517 : Nat := 4983230072969 + 3 ^ 40 * 2722517 * 2
def baseEnd_2722517 : Nat := 931973207357886582277919

theorem tailTrace_2722517 : CollatzResearch.WordTrace tailWord_2722517 prefixEnd_2722517 931973207357886582277919 := by
  unfold tailWord_2722517
  simp only [CollatzResearch.WordTrace]
  refine ⟨99298352677793352730645805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66198901785195568487097203 99298352677793352730645805)
  ·
    refine ⟨37236882254172507273992177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99298352677793352730645805 37236882254172507273992177)
    ·
      refine ⟨27927661690629380455494133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37236882254172507273992177 27927661690629380455494133)
      ·
        refine ⟨2618218283496504417702575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27927661690629380455494133 2618218283496504417702575)
        ·
          refine ⟨3927327425244756626553863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2618218283496504417702575 3927327425244756626553863)
          ·
            refine ⟨5890991137867134939830795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3927327425244756626553863 5890991137867134939830795)
            ·
              refine ⟨8836486706800702409746193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5890991137867134939830795 8836486706800702409746193)
              ·
                refine ⟨6627365030100526807309645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8836486706800702409746193 6627365030100526807309645)
                ·
                  refine ⟨2485261886287697552741117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6627365030100526807309645 2485261886287697552741117)
                  ·
                    refine ⟨931973207357886582277919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2485261886287697552741117 931973207357886582277919)
                    ·
                      rfl

theorem cell22_2722517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_2722517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2722517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2722517 prefixEnd_2722517 := by exact prefixLift 2722517
  have htrace : WordTrace (prefixWord ++ tailWord_2722517) baseStart_2722517 baseEnd_2722517 := by
    simpa [prefixWord, tailWord_2722517, baseEnd_2722517] using wordTrace_append hprefix tailTrace_2722517
  have hstable : (prefixWord ++ tailWord_2722517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722517).length < 2 ^ (prefixWord ++ tailWord_2722517).sum := by decide
  have hdescent : baseEnd_2722517 < baseStart_2722517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722588 : List Nat := [2, 2, 3, 1, 1, 3, 2, 1, 1, 6]
def baseStart_2722588 : Nat := 118140960795 + 2722588 * 2 ^ 59
def prefixEnd_2722588 : Nat := 4983230072969 + 3 ^ 40 * 2722588 * 2
def baseEnd_2722588 : Nat := 931997512108866063752701

theorem tailTrace_2722588 : CollatzResearch.WordTrace tailWord_2722588 prefixEnd_2722588 931997512108866063752701 := by
  unfold tailWord_2722588
  simp only [CollatzResearch.WordTrace]
  refine ⟨49650471130268065928240209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66200628173690754570986945 49650471130268065928240209)
  ·
    refine ⟨37237853347701049446180157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49650471130268065928240209 37237853347701049446180157)
    ·
      refine ⟨13964195005387893542317559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37237853347701049446180157 13964195005387893542317559)
      ·
        refine ⟨20946292508081840313476339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13964195005387893542317559 20946292508081840313476339)
        ·
          refine ⟨31419438762122760470214509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20946292508081840313476339 31419438762122760470214509)
          ·
            refine ⟨11782289535796035176330441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31419438762122760470214509 11782289535796035176330441)
            ·
              refine ⟨8836717151847026382247831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11782289535796035176330441 8836717151847026382247831)
              ·
                refine ⟨13255075727770539573371747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8836717151847026382247831 13255075727770539573371747)
                ·
                  refine ⟨19882613591655809360057621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13255075727770539573371747 19882613591655809360057621)
                  ·
                    refine ⟨931997512108866063752701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19882613591655809360057621 931997512108866063752701)
                    ·
                      rfl

theorem cell22_2722588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_2722588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2722588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2722588 prefixEnd_2722588 := by exact prefixLift 2722588
  have htrace : WordTrace (prefixWord ++ tailWord_2722588) baseStart_2722588 baseEnd_2722588 := by
    simpa [prefixWord, tailWord_2722588, baseEnd_2722588] using wordTrace_append hprefix tailTrace_2722588
  have hstable : (prefixWord ++ tailWord_2722588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722588).length < 2 ^ (prefixWord ++ tailWord_2722588).sum := by decide
  have hdescent : baseEnd_2722588 < baseStart_2722588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722592 : List Nat := [2, 1, 1, 5, 1, 4, 1, 3, 4]
def baseStart_2722592 : Nat := 118140960795 + 2722592 * 2 ^ 59
def prefixEnd_2722592 : Nat := 4983230072969 + 3 ^ 40 * 2722592 * 2
def baseEnd_2722592 : Nat := 310666293796870462217563

theorem tailTrace_2722592 : CollatzResearch.WordTrace tailWord_2722592 prefixEnd_2722592 310666293796870462217563 := by
  unfold tailWord_2722592
  simp only [CollatzResearch.WordTrace]
  refine ⟨49650544076260820269813015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66200725435014427026417353 49650544076260820269813015)
  ·
    refine ⟨74475816114391230404719523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49650544076260820269813015 74475816114391230404719523)
    ·
      refine ⟨111713724171586845607079285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74475816114391230404719523 111713724171586845607079285)
      ·
        refine ⟨10473161641086266775663683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111713724171586845607079285 10473161641086266775663683)
        ·
          refine ⟨15709742461629400163495525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10473161641086266775663683 15709742461629400163495525)
          ·
            refine ⟨2945576711555512530655411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15709742461629400163495525 2945576711555512530655411)
            ·
              refine ⟨4418365067333268795983117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2945576711555512530655411 4418365067333268795983117)
              ·
                refine ⟨1656886900249975798493669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4418365067333268795983117 1656886900249975798493669)
                ·
                  refine ⟨310666293796870462217563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1656886900249975798493669 310666293796870462217563)
                  ·
                    rfl

theorem cell22_2722592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 3, 4].length) (baseStart_2722592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2722592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2722592 prefixEnd_2722592 := by exact prefixLift 2722592
  have htrace : WordTrace (prefixWord ++ tailWord_2722592) baseStart_2722592 baseEnd_2722592 := by
    simpa [prefixWord, tailWord_2722592, baseEnd_2722592] using wordTrace_append hprefix tailTrace_2722592
  have hstable : (prefixWord ++ tailWord_2722592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722592).length < 2 ^ (prefixWord ++ tailWord_2722592).sum := by decide
  have hdescent : baseEnd_2722592 < baseStart_2722592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722601 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 1, 9]
def baseStart_2722601 : Nat := 118140960795 + 2722601 * 2 ^ 59
def prefixEnd_2722601 : Nat := 4983230072969 + 3 ^ 40 * 2722601 * 2
def baseEnd_2722601 : Nat := 932001962274538363177661

theorem tailTrace_2722601 : CollatzResearch.WordTrace tailWord_2722601 prefixEnd_2722601 932001962274538363177661 := by
  unfold tailWord_2722601
  simp only [CollatzResearch.WordTrace]
  refine ⟨99301416409489035076703657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66200944272992690051135771 99301416409489035076703657)
  ·
    refine ⟨74476062307116776307527743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99301416409489035076703657 74476062307116776307527743)
    ·
      refine ⟨111714093460675164461291615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74476062307116776307527743 111714093460675164461291615)
      ·
        refine ⟨167571140191012746691937423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111714093460675164461291615 167571140191012746691937423)
        ·
          refine ⟨251356710286519120037906135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167571140191012746691937423 251356710286519120037906135)
          ·
            refine ⟨377035065429778680056859203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251356710286519120037906135 377035065429778680056859203)
            ·
              refine ⟨565552598144668020085288805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377035065429778680056859203 565552598144668020085288805)
              ·
                refine ⟨106041112152125253765991651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 565552598144668020085288805 106041112152125253765991651)
                ·
                  refine ⟨159061668228187880648987477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106041112152125253765991651 159061668228187880648987477)
                  ·
                    refine ⟨932001962274538363177661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 159061668228187880648987477 932001962274538363177661)
                    ·
                      rfl

theorem cell22_2722601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 9].length) (baseStart_2722601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2722601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2722601 prefixEnd_2722601 := by exact prefixLift 2722601
  have htrace : WordTrace (prefixWord ++ tailWord_2722601) baseStart_2722601 baseEnd_2722601 := by
    simpa [prefixWord, tailWord_2722601, baseEnd_2722601] using wordTrace_append hprefix tailTrace_2722601
  have hstable : (prefixWord ++ tailWord_2722601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722601).length < 2 ^ (prefixWord ++ tailWord_2722601).sum := by decide
  have hdescent : baseEnd_2722601 < baseStart_2722601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722693 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 8]
def baseStart_2722693 : Nat := 118140960795 + 2722693 * 2 ^ 59
def prefixEnd_2722693 : Nat := 4983230072969 + 3 ^ 40 * 2722693 * 2
def baseEnd_2722693 : Nat := 310677818584893596625793

theorem tailTrace_2722693 : CollatzResearch.WordTrace tailWord_2722693 prefixEnd_2722693 310677818584893596625793 := by
  unfold tailWord_2722693
  simp only [CollatzResearch.WordTrace]
  refine ⟨99304771925155734789052733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66203181283437156526035155 99304771925155734789052733)
  ·
    refine ⟨37239289471933400545894775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99304771925155734789052733 37239289471933400545894775)
    ·
      refine ⟨55858934207900100818842163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37239289471933400545894775 55858934207900100818842163)
      ·
        refine ⟨83788401311850151228263245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55858934207900100818842163 83788401311850151228263245)
        ·
          refine ⟨31420650491943806710598717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83788401311850151228263245 31420650491943806710598717)
          ·
            refine ⟨11782743934478927516474519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31420650491943806710598717 11782743934478927516474519)
            ·
              refine ⟨17674115901718391274711779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11782743934478927516474519 17674115901718391274711779)
              ·
                refine ⟨26511173852577586912067669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17674115901718391274711779 26511173852577586912067669)
                ·
                  refine ⟨310677818584893596625793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26511173852577586912067669 310677818584893596625793)
                  ·
                    rfl

theorem cell22_2722693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 8].length) (baseStart_2722693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2722693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2722693 prefixEnd_2722693 := by exact prefixLift 2722693
  have htrace : WordTrace (prefixWord ++ tailWord_2722693) baseStart_2722693 baseEnd_2722693 := by
    simpa [prefixWord, tailWord_2722693, baseEnd_2722693] using wordTrace_append hprefix tailTrace_2722693
  have hstable : (prefixWord ++ tailWord_2722693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722693).length < 2 ^ (prefixWord ++ tailWord_2722693).sum := by decide
  have hdescent : baseEnd_2722693 < baseStart_2722693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722695 : List Nat := [1, 1, 4, 2, 3, 1, 2, 1, 3, 4]
def baseStart_2722695 : Nat := 118140960795 + 2722695 * 2 ^ 59
def prefixEnd_2722695 : Nat := 4983230072969 + 3 ^ 40 * 2722695 * 2
def baseEnd_2722695 : Nat := 932034140395553451327373

theorem tailTrace_2722695 : CollatzResearch.WordTrace tailWord_2722695 prefixEnd_2722695 932034140395553451327373 := by
  unfold tailWord_2722695
  simp only [CollatzResearch.WordTrace]
  refine ⟨99304844871148489130625539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66203229914098992753750359 99304844871148489130625539)
  ·
    refine ⟨148957267306722733695938309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99304844871148489130625539 148957267306722733695938309)
    ·
      refine ⟨27929487620010512567988433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148957267306722733695938309 27929487620010512567988433)
      ·
        refine ⟨20947115715007884425991325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27929487620010512567988433 20947115715007884425991325)
        ·
          refine ⟨7855168393127956659746747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20947115715007884425991325 7855168393127956659746747)
          ·
            refine ⟨11782752589691934989620121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7855168393127956659746747 11782752589691934989620121)
            ·
              refine ⟨8837064442268951242215091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11782752589691934989620121 8837064442268951242215091)
              ·
                refine ⟨13255596663403426863322637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8837064442268951242215091 13255596663403426863322637)
                ·
                  refine ⟨4970848748776285073745989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13255596663403426863322637 4970848748776285073745989)
                  ·
                    refine ⟨932034140395553451327373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4970848748776285073745989 932034140395553451327373)
                    ·
                      rfl

theorem cell22_2722695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_2722695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2722695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2722695 prefixEnd_2722695 := by exact prefixLift 2722695
  have htrace : WordTrace (prefixWord ++ tailWord_2722695) baseStart_2722695 baseEnd_2722695 := by
    simpa [prefixWord, tailWord_2722695, baseEnd_2722695] using wordTrace_append hprefix tailTrace_2722695
  have hstable : (prefixWord ++ tailWord_2722695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722695).length < 2 ^ (prefixWord ++ tailWord_2722695).sum := by decide
  have hdescent : baseEnd_2722695 < baseStart_2722695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722727 : List Nat := [1, 1, 6, 1, 3, 1, 2, 1, 6]
def baseStart_2722727 : Nat := 118140960795 + 2722727 * 2 ^ 59
def prefixEnd_2722727 : Nat := 4983230072969 + 3 ^ 40 * 2722727 * 2
def baseEnd_2722727 : Nat := 310681698216505344842425

theorem tailTrace_2722727 : CollatzResearch.WordTrace tailWord_2722727 prefixEnd_2722727 310681698216505344842425 := by
  unfold tailWord_2722727
  simp only [CollatzResearch.WordTrace]
  refine ⟨99306012007032558595790435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66204008004688372397193623 99306012007032558595790435)
  ·
    refine ⟨148959018010548837893685653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99306012007032558595790435 148959018010548837893685653)
    ·
      refine ⟨6982453969244476776266515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 148959018010548837893685653 6982453969244476776266515)
      ·
        refine ⟨10473680953866715164399773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6982453969244476776266515 10473680953866715164399773)
        ·
          refine ⟨3927630357700018186649915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10473680953866715164399773 3927630357700018186649915)
          ·
            refine ⟨5891445536550027279974873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3927630357700018186649915 5891445536550027279974873)
            ·
              refine ⟨4418584152412520459981155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5891445536550027279974873 4418584152412520459981155)
              ·
                refine ⟨6627876228618780689971733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4418584152412520459981155 6627876228618780689971733)
                ·
                  refine ⟨310681698216505344842425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6627876228618780689971733 310681698216505344842425)
                  ·
                    rfl

theorem cell22_2722727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 6].length) (baseStart_2722727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2722727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2722727 prefixEnd_2722727 := by exact prefixLift 2722727
  have htrace : WordTrace (prefixWord ++ tailWord_2722727) baseStart_2722727 baseEnd_2722727 := by
    simpa [prefixWord, tailWord_2722727, baseEnd_2722727] using wordTrace_append hprefix tailTrace_2722727
  have hstable : (prefixWord ++ tailWord_2722727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722727).length < 2 ^ (prefixWord ++ tailWord_2722727).sum := by decide
  have hdescent : baseEnd_2722727 < baseStart_2722727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722768 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 1, 8]
def baseStart_2722768 : Nat := 118140960795 + 2722768 * 2 ^ 59
def prefixEnd_2722768 : Nat := 4983230072969 + 3 ^ 40 * 2722768 * 2
def baseEnd_2722768 : Nat := 932059129787405594252149

theorem tailTrace_2722768 : CollatzResearch.WordTrace tailWord_2722768 prefixEnd_2722768 932059129787405594252149 := by
  unfold tailWord_2722768
  simp only [CollatzResearch.WordTrace]
  refine ⟨49653753699942011299016479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66205004933256015065355305 49653753699942011299016479)
  ·
    refine ⟨74480630549913016948524719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49653753699942011299016479 74480630549913016948524719)
    ·
      refine ⟨111720945824869525422787079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74480630549913016948524719 111720945824869525422787079)
      ·
        refine ⟨167581418737304288134180619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111720945824869525422787079 167581418737304288134180619)
        ·
          refine ⟨251372128105956432201270929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167581418737304288134180619 251372128105956432201270929)
          ·
            refine ⟨188529096079467324150953197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251372128105956432201270929 188529096079467324150953197)
            ·
              refine ⟨70698411029800246556607449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 188529096079467324150953197 70698411029800246556607449)
              ·
                refine ⟨53023808272350184917455587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70698411029800246556607449 53023808272350184917455587)
                ·
                  refine ⟨79535712408525277376183381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53023808272350184917455587 79535712408525277376183381)
                  ·
                    refine ⟨932059129787405594252149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 79535712408525277376183381 932059129787405594252149)
                    ·
                      rfl

theorem cell22_2722768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 8].length) (baseStart_2722768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2722768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2722768 prefixEnd_2722768 := by exact prefixLift 2722768
  have htrace : WordTrace (prefixWord ++ tailWord_2722768) baseStart_2722768 baseEnd_2722768 := by
    simpa [prefixWord, tailWord_2722768, baseEnd_2722768] using wordTrace_append hprefix tailTrace_2722768
  have hstable : (prefixWord ++ tailWord_2722768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722768).length < 2 ^ (prefixWord ++ tailWord_2722768).sum := by decide
  have hdescent : baseEnd_2722768 < baseStart_2722768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722774 : List Nat := [5, 2, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_2722774 : Nat := 118140960795 + 2722774 * 2 ^ 59
def prefixEnd_2722774 : Nat := 4983230072969 + 3 ^ 40 * 2722774 * 2
def baseEnd_2722774 : Nat := 932061183710023578602131

theorem tailTrace_2722774 : CollatzResearch.WordTrace tailWord_2722774 prefixEnd_2722774 932061183710023578602131 := by
  unfold tailWord_2722774
  simp only [CollatzResearch.WordTrace]
  refine ⟨6206732889866392851421961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66205150825241523748500917 6206732889866392851421961)
  ·
    refine ⟨4655049667399794638566471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6206732889866392851421961 4655049667399794638566471)
    ·
      refine ⟨6982574501099691957849707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4655049667399794638566471 6982574501099691957849707)
      ·
        refine ⟨10473861751649537936774561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6982574501099691957849707 10473861751649537936774561)
        ·
          refine ⟨7855396313737153452580921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10473861751649537936774561 7855396313737153452580921)
          ·
            refine ⟨5891547235302865089435691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7855396313737153452580921 5891547235302865089435691)
            ·
              refine ⟨8837320852954297634153537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5891547235302865089435691 8837320852954297634153537)
              ·
                refine ⟨6627990639715723225615153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8837320852954297634153537 6627990639715723225615153)
                ·
                  refine ⟨4970992979786792419211365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6627990639715723225615153 4970992979786792419211365)
                  ·
                    refine ⟨932061183710023578602131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4970992979786792419211365 932061183710023578602131)
                    ·
                      rfl

theorem cell22_2722774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_2722774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2722774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2722774 prefixEnd_2722774 := by exact prefixLift 2722774
  have htrace : WordTrace (prefixWord ++ tailWord_2722774) baseStart_2722774 baseEnd_2722774 := by
    simpa [prefixWord, tailWord_2722774, baseEnd_2722774] using wordTrace_append hprefix tailTrace_2722774
  have hstable : (prefixWord ++ tailWord_2722774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722774).length < 2 ^ (prefixWord ++ tailWord_2722774).sum := by decide
  have hdescent : baseEnd_2722774 < baseStart_2722774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722862 : List Nat := [4, 1, 3, 1, 1, 1, 3, 2, 6]
def baseStart_2722862 : Nat := 118140960795 + 2722862 * 2 ^ 59
def prefixEnd_2722862 : Nat := 4983230072969 + 3 ^ 40 * 2722862 * 2
def baseEnd_2722862 : Nat := 310697102636140227467287

theorem tailTrace_2722862 : CollatzResearch.WordTrace tailWord_2722862 prefixEnd_2722862 310697102636140227467287 := by
  unfold tailWord_2722862
  simp only [CollatzResearch.WordTrace]
  refine ⟨12413866982692934581494355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66207290574362317767969893 12413866982692934581494355)
  ·
    refine ⟨18620800474039401872241533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12413866982692934581494355 18620800474039401872241533)
    ·
      refine ⟨6982800177764775702090575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18620800474039401872241533 6982800177764775702090575)
      ·
        refine ⟨10474200266647163553135863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6982800177764775702090575 10474200266647163553135863)
        ·
          refine ⟨15711300399970745329703795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10474200266647163553135863 15711300399970745329703795)
          ·
            refine ⟨23566950599956117994555693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15711300399970745329703795 23566950599956117994555693)
            ·
              refine ⟨8837606474983544247958385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23566950599956117994555693 8837606474983544247958385)
              ·
                refine ⟨6628204856237658185968789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8837606474983544247958385 6628204856237658185968789)
                ·
                  refine ⟨310697102636140227467287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6628204856237658185968789 310697102636140227467287)
                  ·
                    rfl

theorem cell22_2722862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_2722862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2722862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2722862 prefixEnd_2722862 := by exact prefixLift 2722862
  have htrace : WordTrace (prefixWord ++ tailWord_2722862) baseStart_2722862 baseEnd_2722862 := by
    simpa [prefixWord, tailWord_2722862, baseEnd_2722862] using wordTrace_append hprefix tailTrace_2722862
  have hstable : (prefixWord ++ tailWord_2722862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722862).length < 2 ^ (prefixWord ++ tailWord_2722862).sum := by decide
  have hdescent : baseEnd_2722862 < baseStart_2722862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722877 : List Nat := [1, 4, 1, 3, 1, 2, 2, 2, 1, 5]
def baseStart_2722877 : Nat := 118140960795 + 2722877 * 2 ^ 59
def prefixEnd_2722877 : Nat := 4983230072969 + 3 ^ 40 * 2722877 * 2
def baseEnd_2722877 : Nat := 932096442714965643276815

theorem tailTrace_2722877 : CollatzResearch.WordTrace tailWord_2722877 prefixEnd_2722877 932096442714965643276815 := by
  unfold tailWord_2722877
  simp only [CollatzResearch.WordTrace]
  refine ⟨99311482956489134213750885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66207655304326089475833923 99311482956489134213750885)
  ·
    refine ⟨18620903054341712665078291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99311482956489134213750885 18620903054341712665078291)
    ·
      refine ⟨27931354581512568997617437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18620903054341712665078291 27931354581512568997617437)
      ·
        refine ⟨10474257968067213374106539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27931354581512568997617437 10474257968067213374106539)
        ·
          refine ⟨15711386952100820061159809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10474257968067213374106539 15711386952100820061159809)
          ·
            refine ⟨11783540214075615045869857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15711386952100820061159809 11783540214075615045869857)
            ·
              refine ⟨8837655160556711284402393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11783540214075615045869857 8837655160556711284402393)
              ·
                refine ⟨6628241370417533463301795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8837655160556711284402393 6628241370417533463301795)
                ·
                  refine ⟨9942362055626300194952693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6628241370417533463301795 9942362055626300194952693)
                  ·
                    refine ⟨932096442714965643276815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9942362055626300194952693 932096442714965643276815)
                    ·
                      rfl

theorem cell22_2722877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_2722877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2722877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2722877 prefixEnd_2722877 := by exact prefixLift 2722877
  have htrace : WordTrace (prefixWord ++ tailWord_2722877) baseStart_2722877 baseEnd_2722877 := by
    simpa [prefixWord, tailWord_2722877, baseEnd_2722877] using wordTrace_append hprefix tailTrace_2722877
  have hstable : (prefixWord ++ tailWord_2722877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722877).length < 2 ^ (prefixWord ++ tailWord_2722877).sum := by decide
  have hdescent : baseEnd_2722877 < baseStart_2722877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722935 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 9]
def baseStart_2722935 : Nat := 118140960795 + 2722935 * 2 ^ 59
def prefixEnd_2722935 : Nat := 4983230072969 + 3 ^ 40 * 2722935 * 2
def baseEnd_2722935 : Nat := 310705432433424275108879

theorem tailTrace_2722935 : CollatzResearch.WordTrace tailWord_2722935 prefixEnd_2722935 310705432433424275108879 := by
  unfold tailWord_2722935
  simp only [CollatzResearch.WordTrace]
  refine ⟨99313598390279010119362259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66209065593519340079574839 99313598390279010119362259)
  ·
    refine ⟨148970397585418515179043389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99313598390279010119362259 148970397585418515179043389)
    ·
      refine ⟨55863899094531943192141271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148970397585418515179043389 55863899094531943192141271)
      ·
        refine ⟨83795848641797914788211907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55863899094531943192141271 83795848641797914788211907)
        ·
          refine ⟨125693772962696872182317861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83795848641797914788211907 125693772962696872182317861)
          ·
            refine ⟨23567582430505663534184599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125693772962696872182317861 23567582430505663534184599)
            ·
              refine ⟨35351373645758495301276899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23567582430505663534184599 35351373645758495301276899)
              ·
                refine ⟨53027060468637742951915349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35351373645758495301276899 53027060468637742951915349)
                ·
                  refine ⟨310705432433424275108879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53027060468637742951915349 310705432433424275108879)
                  ·
                    rfl

theorem cell22_2722935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 9].length) (baseStart_2722935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2722935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2722935 prefixEnd_2722935 := by exact prefixLift 2722935
  have htrace : WordTrace (prefixWord ++ tailWord_2722935) baseStart_2722935 baseEnd_2722935 := by
    simpa [prefixWord, tailWord_2722935, baseEnd_2722935] using wordTrace_append hprefix tailTrace_2722935
  have hstable : (prefixWord ++ tailWord_2722935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722935).length < 2 ^ (prefixWord ++ tailWord_2722935).sum := by decide
  have hdescent : baseEnd_2722935 < baseStart_2722935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723029 : List Nat := [1, 3, 2, 4, 1, 1, 1, 3, 1, 5]
def baseStart_2723029 : Nat := 118140960795 + 2723029 * 2 ^ 59
def prefixEnd_2723029 : Nat := 4983230072969 + 3 ^ 40 * 2723029 * 2
def baseEnd_2723029 : Nat := 932148475421287913476349

theorem tailTrace_2723029 : CollatzResearch.WordTrace tailWord_2723029 prefixEnd_2723029 932148475421287913476349 := by
  unfold tailWord_2723029
  simp only [CollatzResearch.WordTrace]
  refine ⟨99317026851938464173284141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66211351234625642782189427 99317026851938464173284141)
  ·
    refine ⟨37243885069476924064981553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99317026851938464173284141 37243885069476924064981553)
    ·
      refine ⟨27932913802107693048736165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37243885069476924064981553 27932913802107693048736165)
      ·
        refine ⟨5237421337895192446638031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27932913802107693048736165 5237421337895192446638031)
        ·
          refine ⟨7856132006842788669957047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5237421337895192446638031 7856132006842788669957047)
          ·
            refine ⟨11784198010264183004935571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7856132006842788669957047 11784198010264183004935571)
            ·
              refine ⟨17676297015396274507403357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11784198010264183004935571 17676297015396274507403357)
              ·
                refine ⟨6628611380773602940276259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17676297015396274507403357 6628611380773602940276259)
                ·
                  refine ⟨9942917071160404410414389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6628611380773602940276259 9942917071160404410414389)
                  ·
                    refine ⟨932148475421287913476349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9942917071160404410414389 932148475421287913476349)
                    ·
                      rfl

theorem cell22_2723029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_2723029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2723029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2723029 prefixEnd_2723029 := by exact prefixLift 2723029
  have htrace : WordTrace (prefixWord ++ tailWord_2723029) baseStart_2723029 baseEnd_2723029 := by
    simpa [prefixWord, tailWord_2723029, baseEnd_2723029] using wordTrace_append hprefix tailTrace_2723029
  have hstable : (prefixWord ++ tailWord_2723029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723029).length < 2 ^ (prefixWord ++ tailWord_2723029).sum := by decide
  have hdescent : baseEnd_2723029 < baseStart_2723029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723044 : List Nat := [2, 3, 1, 1, 1, 2, 5, 1, 2, 4]
def baseStart_2723044 : Nat := 118140960795 + 2723044 * 2 ^ 59
def prefixEnd_2723044 : Nat := 4983230072969 + 3 ^ 40 * 2723044 * 2
def baseEnd_2723044 : Nat := 932153610227832874351303

theorem tailTrace_2723044 : CollatzResearch.WordTrace tailWord_2723044 prefixEnd_2723044 932153610227832874351303 := by
  unfold tailWord_2723044
  simp only [CollatzResearch.WordTrace]
  refine ⟨49658786973442060867540093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66211715964589414490053457 49658786973442060867540093)
  ·
    refine ⟨18622045115040772825327535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49658786973442060867540093 18622045115040772825327535)
    ·
      refine ⟨27933067672561159237991303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18622045115040772825327535 27933067672561159237991303)
      ·
        refine ⟨41899601508841738856986955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27933067672561159237991303 41899601508841738856986955)
        ·
          refine ⟨62849402263262608285480433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41899601508841738856986955 62849402263262608285480433)
          ·
            refine ⟨47137051697446956214110325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62849402263262608285480433 47137051697446956214110325)
            ·
              refine ⟨4419098596635652145072843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47137051697446956214110325 4419098596635652145072843)
              ·
                refine ⟨6628647894953478217609265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4419098596635652145072843 6628647894953478217609265)
                ·
                  refine ⟨4971485921215108663206949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6628647894953478217609265 4971485921215108663206949)
                  ·
                    refine ⟨932153610227832874351303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4971485921215108663206949 932153610227832874351303)
                    ·
                      rfl

theorem cell22_2723044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_2723044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2723044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2723044 prefixEnd_2723044 := by exact prefixLift 2723044
  have htrace : WordTrace (prefixWord ++ tailWord_2723044) baseStart_2723044 baseEnd_2723044 := by
    simpa [prefixWord, tailWord_2723044, baseEnd_2723044] using wordTrace_append hprefix tailTrace_2723044
  have hstable : (prefixWord ++ tailWord_2723044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723044).length < 2 ^ (prefixWord ++ tailWord_2723044).sum := by decide
  have hdescent : baseEnd_2723044 < baseStart_2723044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723125 : List Nat := [1, 3, 3, 1, 2, 3, 3, 2, 1, 3]
def baseStart_2723125 : Nat := 118140960795 + 2723125 * 2 ^ 59
def prefixEnd_2723125 : Nat := 4983230072969 + 3 ^ 40 * 2723125 * 2
def baseEnd_2723125 : Nat := 932181338183175663076055

theorem tailTrace_2723125 : CollatzResearch.WordTrace tailWord_2723125 prefixEnd_2723125 932181338183175663076055 := by
  unfold tailWord_2723125
  simp only [CollatzResearch.WordTrace]
  refine ⟨99320528259590672568778829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66213685506393781712519219 99320528259590672568778829)
  ·
    refine ⟨37245198097346502213292061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99320528259590672568778829 37245198097346502213292061)
    ·
      refine ⟨13966949286504938329984523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37245198097346502213292061 13966949286504938329984523)
      ·
        refine ⟨20950423929757407494976785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13966949286504938329984523 20950423929757407494976785)
        ·
          refine ⟨15712817947318055621232589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20950423929757407494976785 15712817947318055621232589)
          ·
            refine ⟨5892306730244270857962221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15712817947318055621232589 5892306730244270857962221)
            ·
              refine ⟨2209615023841601571735833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5892306730244270857962221 2209615023841601571735833)
              ·
                refine ⟨1657211267881201178801875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2209615023841601571735833 1657211267881201178801875)
                ·
                  refine ⟨2485816901821801768202813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1657211267881201178801875 2485816901821801768202813)
                  ·
                    refine ⟨932181338183175663076055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2485816901821801768202813 932181338183175663076055)
                    ·
                      rfl

theorem cell22_2723125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_2723125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2723125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2723125 prefixEnd_2723125 := by exact prefixLift 2723125
  have htrace : WordTrace (prefixWord ++ tailWord_2723125) baseStart_2723125 baseEnd_2723125 := by
    simpa [prefixWord, tailWord_2723125, baseEnd_2723125] using wordTrace_append hprefix tailTrace_2723125
  have hstable : (prefixWord ++ tailWord_2723125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723125).length < 2 ^ (prefixWord ++ tailWord_2723125).sum := by decide
  have hdescent : baseEnd_2723125 < baseStart_2723125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723168 : List Nat := [2, 1, 1, 3, 4, 2, 3, 1, 1, 4]
def baseStart_2723168 : Nat := 118140960795 + 2723168 * 2 ^ 59
def prefixEnd_2723168 : Nat := 4983230072969 + 3 ^ 40 * 2723168 * 2
def baseEnd_2723168 : Nat := 932196057961937884250923

theorem tailTrace_2723168 : CollatzResearch.WordTrace tailWord_2723168 prefixEnd_2723168 932196057961937884250923 := by
  unfold tailWord_2723168
  simp only [CollatzResearch.WordTrace]
  refine ⟨49661048299217445456297079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66214731065623260608396105 49661048299217445456297079)
  ·
    refine ⟨74491572448826168184445619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49661048299217445456297079 74491572448826168184445619)
    ·
      refine ⟨111737358673239252276668429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74491572448826168184445619 111737358673239252276668429)
      ·
        refine ⟨41901509502464719603750661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111737358673239252276668429 41901509502464719603750661)
        ·
          refine ⟨7856533031712134925703249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41901509502464719603750661 7856533031712134925703249)
          ·
            refine ⟨5892399773784101194277437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7856533031712134925703249 5892399773784101194277437)
            ·
              refine ⟨2209649915169037947854039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5892399773784101194277437 2209649915169037947854039)
              ·
                refine ⟨3314474872753556921781059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2209649915169037947854039 3314474872753556921781059)
                ·
                  refine ⟨4971712309130335382671589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3314474872753556921781059 4971712309130335382671589)
                  ·
                    refine ⟨932196057961937884250923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4971712309130335382671589 932196057961937884250923)
                    ·
                      rfl

theorem cell22_2723168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 1, 4].length) (baseStart_2723168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2723168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2723168 prefixEnd_2723168 := by exact prefixLift 2723168
  have htrace : WordTrace (prefixWord ++ tailWord_2723168) baseStart_2723168 baseEnd_2723168 := by
    simpa [prefixWord, tailWord_2723168, baseEnd_2723168] using wordTrace_append hprefix tailTrace_2723168
  have hstable : (prefixWord ++ tailWord_2723168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723168).length < 2 ^ (prefixWord ++ tailWord_2723168).sum := by decide
  have hdescent : baseEnd_2723168 < baseStart_2723168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723226 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 5, 3]
def baseStart_2723226 : Nat := 118140960795 + 2723226 * 2 ^ 59
def prefixEnd_2723226 : Nat := 4983230072969 + 3 ^ 40 * 2723226 * 2
def baseEnd_2723226 : Nat := 932215912547245066300745

theorem tailTrace_2723226 : CollatzResearch.WordTrace tailWord_2723226 prefixEnd_2723226 932215912547245066300745 := by
  unfold tailWord_2723226
  simp only [CollatzResearch.WordTrace]
  refine ⟨24831053008056191704551383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66216141354816511212137021 24831053008056191704551383)
  ·
    refine ⟨37246579512084287556827075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24831053008056191704551383 37246579512084287556827075)
    ·
      refine ⟨55869869268126431335240613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37246579512084287556827075 55869869268126431335240613)
      ·
        refine ⟨10475600487773705875357615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55869869268126431335240613 10475600487773705875357615)
        ·
          refine ⟨15713400731660558813036423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10475600487773705875357615 15713400731660558813036423)
          ·
            refine ⟨23570101097490838219554635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15713400731660558813036423 23570101097490838219554635)
            ·
              refine ⟨35355151646236257329331953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23570101097490838219554635 35355151646236257329331953)
              ·
                refine ⟨26516363734677192996998965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35355151646236257329331953 26516363734677192996998965)
                ·
                  refine ⟨2485909100125986843468653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26516363734677192996998965 2485909100125986843468653)
                  ·
                    refine ⟨932215912547245066300745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2485909100125986843468653 932215912547245066300745)
                    ·
                      rfl

theorem cell22_2723226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 5, 3].length) (baseStart_2723226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2723226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2723226 prefixEnd_2723226 := by exact prefixLift 2723226
  have htrace : WordTrace (prefixWord ++ tailWord_2723226) baseStart_2723226 baseEnd_2723226 := by
    simpa [prefixWord, tailWord_2723226, baseEnd_2723226] using wordTrace_append hprefix tailTrace_2723226
  have hstable : (prefixWord ++ tailWord_2723226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723226).length < 2 ^ (prefixWord ++ tailWord_2723226).sum := by decide
  have hdescent : baseEnd_2723226 < baseStart_2723226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723352 : List Nat := [2, 1, 2, 3, 4, 2, 2, 2, 4]
def baseStart_2723352 : Nat := 118140960795 + 2723352 * 2 ^ 59
def prefixEnd_2723352 : Nat := 4983230072969 + 3 ^ 40 * 2723352 * 2
def baseEnd_2723352 : Nat := 310753014974074245883453

theorem tailTrace_2723352 : CollatzResearch.WordTrace tailWord_2723352 prefixEnd_2723352 310753014974074245883453 := by
  unfold tailWord_2723352
  simp only [CollatzResearch.WordTrace]
  refine ⟨49664403814884145168646155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66219205086512193558194873 49664403814884145168646155)
  ·
    refine ⟨74496605722326217752969233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49664403814884145168646155 74496605722326217752969233)
    ·
      refine ⟨55872454291744663314726925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74496605722326217752969233 55872454291744663314726925)
      ·
        refine ⟨20952170359404248743022597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55872454291744663314726925 20952170359404248743022597)
        ·
          refine ⟨3928531942388296639316737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20952170359404248743022597 3928531942388296639316737)
          ·
            refine ⟨2946398956791222479487553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3928531942388296639316737 2946398956791222479487553)
            ·
              refine ⟨2209799217593416859615665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2946398956791222479487553 2209799217593416859615665)
              ·
                refine ⟨1657349413195062644711749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2209799217593416859615665 1657349413195062644711749)
                ·
                  refine ⟨310753014974074245883453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1657349413195062644711749 310753014974074245883453)
                  ·
                    rfl

theorem cell22_2723352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 2, 4].length) (baseStart_2723352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2723352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2723352 prefixEnd_2723352 := by exact prefixLift 2723352
  have htrace : WordTrace (prefixWord ++ tailWord_2723352) baseStart_2723352 baseEnd_2723352 := by
    simpa [prefixWord, tailWord_2723352, baseEnd_2723352] using wordTrace_append hprefix tailTrace_2723352
  have hstable : (prefixWord ++ tailWord_2723352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723352).length < 2 ^ (prefixWord ++ tailWord_2723352).sum := by decide
  have hdescent : baseEnd_2723352 < baseStart_2723352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723363 : List Nat := [1, 1, 1, 4, 5, 2, 1, 7]
def baseStart_2723363 : Nat := 118140960795 + 2723363 * 2 ^ 59
def prefixEnd_2723363 : Nat := 4983230072969 + 3 ^ 40 * 2723363 * 2
def baseEnd_2723363 : Nat := 103584756716335819513925

theorem tailTrace_2723363 : CollatzResearch.WordTrace tailWord_2723363 prefixEnd_2723363 103584756716335819513925 := by
  unfold tailWord_2723363
  simp only [CollatzResearch.WordTrace]
  refine ⟨99329208832728439215942743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66219472555152292810628495 99329208832728439215942743)
  ·
    refine ⟨148993813249092658823914115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99329208832728439215942743 148993813249092658823914115)
    ·
      refine ⟨223490719873638988235871173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148993813249092658823914115 223490719873638988235871173)
      ·
        refine ⟨41904509976307310294225845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 223490719873638988235871173 41904509976307310294225845)
        ·
          refine ⟨3928547810278810340083673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41904509976307310294225845 3928547810278810340083673)
          ·
            refine ⟨2946410857709107755062755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3928547810278810340083673 2946410857709107755062755)
            ·
              refine ⟨4419616286563661632594133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2946410857709107755062755 4419616286563661632594133)
              ·
                refine ⟨103584756716335819513925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4419616286563661632594133 103584756716335819513925)
                ·
                  rfl

theorem cell22_2723363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 7].length) (baseStart_2723363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2723363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2723363 prefixEnd_2723363 := by exact prefixLift 2723363
  have htrace : WordTrace (prefixWord ++ tailWord_2723363) baseStart_2723363 baseEnd_2723363 := by
    simpa [prefixWord, tailWord_2723363, baseEnd_2723363] using wordTrace_append hprefix tailTrace_2723363
  have hstable : (prefixWord ++ tailWord_2723363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723363).length < 2 ^ (prefixWord ++ tailWord_2723363).sum := by decide
  have hdescent : baseEnd_2723363 < baseStart_2723363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723382 : List Nat := [5, 1, 2, 1, 3, 2, 1, 1, 2, 4]
def baseStart_2723382 : Nat := 118140960795 + 2723382 * 2 ^ 59
def prefixEnd_2723382 : Nat := 4983230072969 + 3 ^ 40 * 2723382 * 2
def baseEnd_2723382 : Nat := 932269314535312659400267

theorem tailTrace_2723382 : CollatzResearch.WordTrace tailWord_2723382 prefixEnd_2723382 932269314535312659400267 := by
  unfold tailWord_2723382
  simp only [CollatzResearch.WordTrace]
  refine ⟨6208118863728725341305275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66219934546439736973922933 6208118863728725341305275)
  ·
    refine ⟨9312178295593088011957913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6208118863728725341305275 9312178295593088011957913)
    ·
      refine ⟨6984133721694816008968435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9312178295593088011957913 6984133721694816008968435)
      ·
        refine ⟨10476200582542224013452653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6984133721694816008968435 10476200582542224013452653)
        ·
          refine ⟨3928575218453334005044745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10476200582542224013452653 3928575218453334005044745)
          ·
            refine ⟨2946431413840000503783559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3928575218453334005044745 2946431413840000503783559)
            ·
              refine ⟨4419647120760000755675339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2946431413840000503783559 4419647120760000755675339)
              ·
                refine ⟨6629470681140001133513009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4419647120760000755675339 6629470681140001133513009)
                ·
                  refine ⟨4972103010855000850134757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6629470681140001133513009 4972103010855000850134757)
                  ·
                    refine ⟨932269314535312659400267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4972103010855000850134757 932269314535312659400267)
                    ·
                      rfl

theorem cell22_2723382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_2723382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2723382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2723382 prefixEnd_2723382 := by exact prefixLift 2723382
  have htrace : WordTrace (prefixWord ++ tailWord_2723382) baseStart_2723382 baseEnd_2723382 := by
    simpa [prefixWord, tailWord_2723382, baseEnd_2723382] using wordTrace_append hprefix tailTrace_2723382
  have hstable : (prefixWord ++ tailWord_2723382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723382).length < 2 ^ (prefixWord ++ tailWord_2723382).sum := by decide
  have hdescent : baseEnd_2723382 < baseStart_2723382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723451 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 3, 5]
def baseStart_2723451 : Nat := 118140960795 + 2723451 * 2 ^ 59
def prefixEnd_2723451 : Nat := 4983230072969 + 3 ^ 40 * 2723451 * 2
def baseEnd_2723451 : Nat := 932292934645419479425055

theorem tailTrace_2723451 : CollatzResearch.WordTrace tailWord_2723451 prefixEnd_2723451 932292934645419479425055 := by
  unfold tailWord_2723451
  simp only [CollatzResearch.WordTrace]
  refine ⟨99332418456409630245146207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66221612304273086830097471 99332418456409630245146207)
  ·
    refine ⟨148998627684614445367719311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99332418456409630245146207 148998627684614445367719311)
    ·
      refine ⟨223497941526921668051578967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148998627684614445367719311 223497941526921668051578967)
      ·
        refine ⟨335246912290382502077368451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223497941526921668051578967 335246912290382502077368451)
        ·
          refine ⟨502870368435573753116052677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335246912290382502077368451 502870368435573753116052677)
          ·
            refine ⟨94288194081670078709259877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 502870368435573753116052677 94288194081670078709259877)
            ·
              refine ⟨17679036390313139757986227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94288194081670078709259877 17679036390313139757986227)
              ·
                refine ⟨26518554585469709636979341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17679036390313139757986227 26518554585469709636979341)
                ·
                  refine ⟨9944457969551141113867253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26518554585469709636979341 9944457969551141113867253)
                  ·
                    refine ⟨932292934645419479425055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9944457969551141113867253 932292934645419479425055)
                    ·
                      rfl

theorem cell22_2723451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 5].length) (baseStart_2723451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2723451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2723451 prefixEnd_2723451 := by exact prefixLift 2723451
  have htrace : WordTrace (prefixWord ++ tailWord_2723451) baseStart_2723451 baseEnd_2723451 := by
    simpa [prefixWord, tailWord_2723451, baseEnd_2723451] using wordTrace_append hprefix tailTrace_2723451
  have hstable : (prefixWord ++ tailWord_2723451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723451).length < 2 ^ (prefixWord ++ tailWord_2723451).sum := by decide
  have hdescent : baseEnd_2723451 < baseStart_2723451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723468 : List Nat := [2, 2, 1, 2, 1, 1, 3, 3, 4, 3]
def baseStart_2723468 : Nat := 118140960795 + 2723468 * 2 ^ 59
def prefixEnd_2723468 : Nat := 4983230072969 + 3 ^ 40 * 2723468 * 2
def baseEnd_2723468 : Nat := 932298754092837101750003

theorem tailTrace_2723468 : CollatzResearch.WordTrace tailWord_2723468 prefixEnd_2723468 932298754092837101750003 := by
  unfold tailWord_2723468
  simp only [CollatzResearch.WordTrace]
  refine ⟨49666519248674021074257529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66222025664898694765676705 49666519248674021074257529)
  ·
    refine ⟨37249889436505515805693147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49666519248674021074257529 37249889436505515805693147)
    ·
      refine ⟨55874834154758273708539721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37249889436505515805693147 55874834154758273708539721)
      ·
        refine ⟨41906125616068705281404791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55874834154758273708539721 41906125616068705281404791)
        ·
          refine ⟨62859188424103057922107187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41906125616068705281404791 62859188424103057922107187)
          ·
            refine ⟨94288782636154586883160781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62859188424103057922107187 94288782636154586883160781)
            ·
              refine ⟨35358293488557970081185293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94288782636154586883160781 35358293488557970081185293)
              ·
                refine ⟨13259360058209238780444485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35358293488557970081185293 13259360058209238780444485)
                ·
                  refine ⟨2486130010914232271333341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13259360058209238780444485 2486130010914232271333341)
                  ·
                    refine ⟨932298754092837101750003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2486130010914232271333341 932298754092837101750003)
                    ·
                      rfl

theorem cell22_2723468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 4, 3].length) (baseStart_2723468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2723468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2723468 prefixEnd_2723468 := by exact prefixLift 2723468
  have htrace : WordTrace (prefixWord ++ tailWord_2723468) baseStart_2723468 baseEnd_2723468 := by
    simpa [prefixWord, tailWord_2723468, baseEnd_2723468] using wordTrace_append hprefix tailTrace_2723468
  have hstable : (prefixWord ++ tailWord_2723468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723468).length < 2 ^ (prefixWord ++ tailWord_2723468).sum := by decide
  have hdescent : baseEnd_2723468 < baseStart_2723468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723470 : List Nat := [4, 1, 1, 3, 1, 4, 1, 1, 6]
def baseStart_2723470 : Nat := 118140960795 + 2723470 * 2 ^ 59
def prefixEnd_2723470 : Nat := 4983230072969 + 3 ^ 40 * 2723470 * 2
def baseEnd_2723470 : Nat := 310766479577903254399999

theorem tailTrace_2723470 : CollatzResearch.WordTrace tailWord_2723470 prefixEnd_2723470 310766479577903254399999 := by
  unfold tailWord_2723470
  simp only [CollatzResearch.WordTrace]
  refine ⟨12416638930417599561260983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66222074295560530993391909 12416638930417599561260983)
  ·
    refine ⟨18624958395626399341891475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12416638930417599561260983 18624958395626399341891475)
    ·
      refine ⟨27937437593439599012837213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18624958395626399341891475 27937437593439599012837213)
      ·
        refine ⟨10476539097539849629813955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27937437593439599012837213 10476539097539849629813955)
        ·
          refine ⟨15714808646309774444720933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10476539097539849629813955 15714808646309774444720933)
          ·
            refine ⟨2946526621183082708385175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15714808646309774444720933 2946526621183082708385175)
            ·
              refine ⟨4419789931774624062577763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2946526621183082708385175 4419789931774624062577763)
              ·
                refine ⟨6629684897661936093866645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4419789931774624062577763 6629684897661936093866645)
                ·
                  refine ⟨310766479577903254399999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6629684897661936093866645 310766479577903254399999)
                  ·
                    rfl

theorem cell22_2723470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_2723470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2723470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2723470 prefixEnd_2723470 := by exact prefixLift 2723470
  have htrace : WordTrace (prefixWord ++ tailWord_2723470) baseStart_2723470 baseEnd_2723470 := by
    simpa [prefixWord, tailWord_2723470, baseEnd_2723470] using wordTrace_append hprefix tailTrace_2723470
  have hstable : (prefixWord ++ tailWord_2723470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723470).length < 2 ^ (prefixWord ++ tailWord_2723470).sum := by decide
  have hdescent : baseEnd_2723470 < baseStart_2723470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723502 : List Nat := [4, 1, 4, 1, 2, 1, 1, 2, 1, 5]
def baseStart_2723502 : Nat := 118140960795 + 2723502 * 2 ^ 59
def prefixEnd_2723502 : Nat := 4983230072969 + 3 ^ 40 * 2723502 * 2
def baseEnd_2723502 : Nat := 932310392987672346399899

theorem tailTrace_2723502 : CollatzResearch.WordTrace tailWord_2723502 prefixEnd_2723502 932310392987672346399899 := by
  unfold tailWord_2723502
  simp only [CollatzResearch.WordTrace]
  refine ⟨12416784822403108244406595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66222852386149910636835173 12416784822403108244406595)
  ·
    refine ⟨18625177233604662366609893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12416784822403108244406595 18625177233604662366609893)
    ·
      refine ⟨3492220731300874193739355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18625177233604662366609893 3492220731300874193739355)
      ·
        refine ⟨5238331096951311290609033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3492220731300874193739355 5238331096951311290609033)
        ·
          refine ⟨3928748322713483467956775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5238331096951311290609033 3928748322713483467956775)
          ·
            refine ⟨5893122484070225201935163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3928748322713483467956775 5893122484070225201935163)
            ·
              refine ⟨8839683726105337802902745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5893122484070225201935163 8839683726105337802902745)
              ·
                refine ⟨6629762794579003352177059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8839683726105337802902745 6629762794579003352177059)
                ·
                  refine ⟨9944644191868505028265589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6629762794579003352177059 9944644191868505028265589)
                  ·
                    refine ⟨932310392987672346399899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9944644191868505028265589 932310392987672346399899)
                    ·
                      rfl

theorem cell22_2723502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_2723502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2723502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2723502 prefixEnd_2723502 := by exact prefixLift 2723502
  have htrace : WordTrace (prefixWord ++ tailWord_2723502) baseStart_2723502 baseEnd_2723502 := by
    simpa [prefixWord, tailWord_2723502, baseEnd_2723502] using wordTrace_append hprefix tailTrace_2723502
  have hstable : (prefixWord ++ tailWord_2723502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723502).length < 2 ^ (prefixWord ++ tailWord_2723502).sum := by decide
  have hdescent : baseEnd_2723502 < baseStart_2723502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723532 : List Nat := [2, 2, 1, 5, 3, 1, 1, 7]
def baseStart_2723532 : Nat := 118140960795 + 2723532 * 2 ^ 59
def prefixEnd_2723532 : Nat := 4983230072969 + 3 ^ 40 * 2723532 * 2
def baseEnd_2723532 : Nat := 103591184733418029794423

theorem tailTrace_2723532 : CollatzResearch.WordTrace tailWord_2723532 prefixEnd_2723532 103591184733418029794423 := by
  unfold tailWord_2723532
  simp only [CollatzResearch.WordTrace]
  refine ⟨49667686384558090539422425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66223581846077454052563233 49667686384558090539422425)
  ·
    refine ⟨37250764788418567904566819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49667686384558090539422425 37250764788418567904566819)
    ·
      refine ⟨55876147182627851856850229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37250764788418567904566819 55876147182627851856850229)
      ·
        refine ⟨5238388798371361111579709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55876147182627851856850229 5238388798371361111579709)
        ·
          refine ⟨1964395799389260416842391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5238388798371361111579709 1964395799389260416842391)
          ·
            refine ⟨2946593699083890625263587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1964395799389260416842391 2946593699083890625263587)
            ·
              refine ⟨4419890548625835937895381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2946593699083890625263587 4419890548625835937895381)
              ·
                refine ⟨103591184733418029794423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4419890548625835937895381 103591184733418029794423)
                ·
                  rfl

theorem cell22_2723532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 7].length) (baseStart_2723532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2723532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2723532 prefixEnd_2723532 := by exact prefixLift 2723532
  have htrace : WordTrace (prefixWord ++ tailWord_2723532) baseStart_2723532 baseEnd_2723532 := by
    simpa [prefixWord, tailWord_2723532, baseEnd_2723532] using wordTrace_append hprefix tailTrace_2723532
  have hstable : (prefixWord ++ tailWord_2723532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723532).length < 2 ^ (prefixWord ++ tailWord_2723532).sum := by decide
  have hdescent : baseEnd_2723532 < baseStart_2723532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723543 : List Nat := [1, 1, 3, 2, 1, 3, 1, 5, 5]
def baseStart_2723543 : Nat := 118140960795 + 2723543 * 2 ^ 59
def prefixEnd_2723543 : Nat := 4983230072969 + 3 ^ 40 * 2723543 * 2
def baseEnd_2723543 : Nat := 310774809375187302041591

theorem tailTrace_2723543 : CollatzResearch.WordTrace tailWord_2723543 prefixEnd_2723543 310774809375187302041591 := by
  unfold tailWord_2723543
  simp only [CollatzResearch.WordTrace]
  refine ⟨99335773972076329957495283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66223849314717553304996855 99335773972076329957495283)
  ·
    refine ⟨149003660958114494936242925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99335773972076329957495283 149003660958114494936242925)
    ·
      refine ⟨55876372859292935601091097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149003660958114494936242925 55876372859292935601091097)
      ·
        refine ⟨41907279644469701700818323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55876372859292935601091097 41907279644469701700818323)
        ·
          refine ⟨62860919466704552551227485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41907279644469701700818323 62860919466704552551227485)
          ·
            refine ⟨23572844800014207206710307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62860919466704552551227485 23572844800014207206710307)
            ·
              refine ⟨35359267200021310810065461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23572844800014207206710307 35359267200021310810065461)
              ·
                refine ⟨3314931300001997888443637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35359267200021310810065461 3314931300001997888443637)
                ·
                  refine ⟨310774809375187302041591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3314931300001997888443637 310774809375187302041591)
                  ·
                    rfl

theorem cell22_2723543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 5].length) (baseStart_2723543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2723543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2723543 prefixEnd_2723543 := by exact prefixLift 2723543
  have htrace : WordTrace (prefixWord ++ tailWord_2723543) baseStart_2723543 baseEnd_2723543 := by
    simpa [prefixWord, tailWord_2723543, baseEnd_2723543] using wordTrace_append hprefix tailTrace_2723543
  have hstable : (prefixWord ++ tailWord_2723543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723543).length < 2 ^ (prefixWord ++ tailWord_2723543).sum := by decide
  have hdescent : baseEnd_2723543 < baseStart_2723543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723603 : List Nat := [1, 1, 1, 2, 1, 3, 2, 5, 1, 5]
def baseStart_2723603 : Nat := 118140960795 + 2723603 * 2 ^ 59
def prefixEnd_2723603 : Nat := 4983230072969 + 3 ^ 40 * 2723603 * 2
def baseEnd_2723603 : Nat := 932344967351741749624589

theorem tailTrace_2723603 : CollatzResearch.WordTrace tailWord_2723603 prefixEnd_2723603 932344967351741749624589 := by
  unfold tailWord_2723603
  simp only [CollatzResearch.WordTrace]
  refine ⟨99337962351858960204679463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66225308234572640136452975 99337962351858960204679463)
  ·
    refine ⟨149006943527788440307019195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99337962351858960204679463 149006943527788440307019195)
    ·
      refine ⟨223510415291682660460528793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149006943527788440307019195 223510415291682660460528793)
      ·
        refine ⟨167632811468761995345396595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223510415291682660460528793 167632811468761995345396595)
        ·
          refine ⟨251449217203142993018094893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167632811468761995345396595 251449217203142993018094893)
          ·
            refine ⟨94293456451178622381785585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 251449217203142993018094893 94293456451178622381785585)
            ·
              refine ⟨70720092338383966786339189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94293456451178622381785585 70720092338383966786339189)
              ·
                refine ⟨6630008656723496886219299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70720092338383966786339189 6630008656723496886219299)
                ·
                  refine ⟨9945012985085245329328949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6630008656723496886219299 9945012985085245329328949)
                  ·
                    refine ⟨932344967351741749624589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9945012985085245329328949 932344967351741749624589)
                    ·
                      rfl

theorem cell22_2723603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 5].length) (baseStart_2723603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2723603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2723603 prefixEnd_2723603 := by exact prefixLift 2723603
  have htrace : WordTrace (prefixWord ++ tailWord_2723603) baseStart_2723603 baseEnd_2723603 := by
    simpa [prefixWord, tailWord_2723603, baseEnd_2723603] using wordTrace_append hprefix tailTrace_2723603
  have hstable : (prefixWord ++ tailWord_2723603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723603).length < 2 ^ (prefixWord ++ tailWord_2723603).sum := by decide
  have hdescent : baseEnd_2723603 < baseStart_2723603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723607 : List Nat := [1, 1, 3, 4, 2, 2, 2, 2, 1, 4]
def baseStart_2723607 : Nat := 118140960795 + 2723607 * 2 ^ 59
def prefixEnd_2723607 : Nat := 4983230072969 + 3 ^ 40 * 2723607 * 2
def baseEnd_2723607 : Nat := 932346336633487072524577

theorem tailTrace_2723607 : CollatzResearch.WordTrace tailWord_2723607 prefixEnd_2723607 932346336633487072524577 := by
  unfold tailWord_2723607
  simp only [CollatzResearch.WordTrace]
  refine ⟨99338108243844468887825075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66225405495896312591883383 99338108243844468887825075)
  ·
    refine ⟨149007162365766703331737613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99338108243844468887825075 149007162365766703331737613)
    ·
      refine ⟨55877685887162513749401605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149007162365766703331737613 55877685887162513749401605)
      ·
        refine ⟨10477066103842971328012801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55877685887162513749401605 10477066103842971328012801)
        ·
          refine ⟨7857799577882228496009601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10477066103842971328012801 7857799577882228496009601)
          ·
            refine ⟨5893349683411671372007201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7857799577882228496009601 5893349683411671372007201)
            ·
              refine ⟨4420012262558753529005401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5893349683411671372007201 4420012262558753529005401)
              ·
                refine ⟨3315009196919065146754051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4420012262558753529005401 3315009196919065146754051)
                ·
                  refine ⟨4972513795378597720131077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3315009196919065146754051 4972513795378597720131077)
                  ·
                    refine ⟨932346336633487072524577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4972513795378597720131077 932346336633487072524577)
                    ·
                      rfl

theorem cell22_2723607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_2723607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2723607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2723607 prefixEnd_2723607 := by exact prefixLift 2723607
  have htrace : WordTrace (prefixWord ++ tailWord_2723607) baseStart_2723607 baseEnd_2723607 := by
    simpa [prefixWord, tailWord_2723607, baseEnd_2723607] using wordTrace_append hprefix tailTrace_2723607
  have hstable : (prefixWord ++ tailWord_2723607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723607).length < 2 ^ (prefixWord ++ tailWord_2723607).sum := by decide
  have hdescent : baseEnd_2723607 < baseStart_2723607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723633 : List Nat := [1, 2, 2, 3, 2, 2, 10]
def baseStart_2723633 : Nat := 118140960795 + 2723633 * 2 ^ 59
def prefixEnd_2723633 : Nat := 4983230072969 + 3 ^ 40 * 2723633 * 2
def baseEnd_2723633 : Nat := 34531675443141913754611

theorem tailTrace_2723633 : CollatzResearch.WordTrace tailWord_2723633 prefixEnd_2723633 34531675443141913754611 := by
  unfold tailWord_2723633
  simp only [CollatzResearch.WordTrace]
  refine ⟨99339056541750275328271553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66226037694500183552181035 99339056541750275328271553)
  ·
    refine ⟨74504292406312706496203665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99339056541750275328271553 74504292406312706496203665)
    ·
      refine ⟨55878219304734529872152749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74504292406312706496203665 55878219304734529872152749)
      ·
        refine ⟨20954332239275448702057281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55878219304734529872152749 20954332239275448702057281)
        ·
          refine ⟨15715749179456586526542961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20954332239275448702057281 15715749179456586526542961)
          ·
            refine ⟨11786811884592439894907221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15715749179456586526542961 11786811884592439894907221)
            ·
              refine ⟨34531675443141913754611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11786811884592439894907221 34531675443141913754611)
              ·
                rfl

theorem cell22_2723633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 10].length) (baseStart_2723633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2723633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2723633 prefixEnd_2723633 := by exact prefixLift 2723633
  have htrace : WordTrace (prefixWord ++ tailWord_2723633) baseStart_2723633 baseEnd_2723633 := by
    simpa [prefixWord, tailWord_2723633, baseEnd_2723633] using wordTrace_append hprefix tailTrace_2723633
  have hstable : (prefixWord ++ tailWord_2723633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723633).length < 2 ^ (prefixWord ++ tailWord_2723633).sum := by decide
  have hdescent : baseEnd_2723633 < baseStart_2723633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723746 : List Nat := [3, 3, 1, 2, 4, 1, 1, 2, 5]
def baseStart_2723746 : Nat := 118140960795 + 2723746 * 2 ^ 59
def prefixEnd_2723746 : Nat := 4983230072969 + 3 ^ 40 * 2723746 * 2
def baseEnd_2723746 : Nat := 310797973058045681099717

theorem tailTrace_2723746 : CollatzResearch.WordTrace tailWord_2723746 prefixEnd_2723746 310797973058045681099717 := by
  unfold tailWord_2723746
  simp only [CollatzResearch.WordTrace]
  refine ⟨24835794497585223906783773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66228785326893930418090061 24835794497585223906783773)
  ·
    refine ⟨9313422936594458965043915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24835794497585223906783773 9313422936594458965043915)
    ·
      refine ⟨13970134404891688447565873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9313422936594458965043915 13970134404891688447565873)
      ·
        refine ⟨10477600803668766335674405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13970134404891688447565873 10477600803668766335674405)
        ·
          refine ⟨1964550150687893687938951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10477600803668766335674405 1964550150687893687938951)
          ·
            refine ⟨2946825226031840531908427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1964550150687893687938951 2946825226031840531908427)
            ·
              refine ⟨4420237839047760797862641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2946825226031840531908427 4420237839047760797862641)
              ·
                refine ⟨3315178379285820598396981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4420237839047760797862641 3315178379285820598396981)
                ·
                  refine ⟨310797973058045681099717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3315178379285820598396981 310797973058045681099717)
                  ·
                    rfl

theorem cell22_2723746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_2723746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2723746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2723746 prefixEnd_2723746 := by exact prefixLift 2723746
  have htrace : WordTrace (prefixWord ++ tailWord_2723746) baseStart_2723746 baseEnd_2723746 := by
    simpa [prefixWord, tailWord_2723746, baseEnd_2723746] using wordTrace_append hprefix tailTrace_2723746
  have hstable : (prefixWord ++ tailWord_2723746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723746).length < 2 ^ (prefixWord ++ tailWord_2723746).sum := by decide
  have hdescent : baseEnd_2723746 < baseStart_2723746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723770 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 6, 4]
def baseStart_2723770 : Nat := 118140960795 + 2723770 * 2 ^ 59
def prefixEnd_2723770 : Nat := 4983230072969 + 3 ^ 40 * 2723770 * 2
def baseEnd_2723770 : Nat := 932402134864608980699077

theorem tailTrace_2723770 : CollatzResearch.WordTrace tailWord_2723770 prefixEnd_2723770 932402134864608980699077 := by
  unfold tailWord_2723770
  simp only [CollatzResearch.WordTrace]
  refine ⟨24836013335563486931502191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66229368894835965150672509 24836013335563486931502191)
  ·
    refine ⟨37254020003345230397253287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24836013335563486931502191 37254020003345230397253287)
    ·
      refine ⟨55881030005017845595879931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37254020003345230397253287 55881030005017845595879931)
      ·
        refine ⟨83821545007526768393819897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55881030005017845595879931 83821545007526768393819897)
        ·
          refine ⟨62866158755645076295364923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83821545007526768393819897 62866158755645076295364923)
          ·
            refine ⟨94299238133467614443047385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62866158755645076295364923 94299238133467614443047385)
            ·
              refine ⟨70724428600100710832285539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94299238133467614443047385 70724428600100710832285539)
              ·
                refine ⟨106086642900151066248428309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70724428600100710832285539 106086642900151066248428309)
                ·
                  refine ⟨4972811385944581230395077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 106086642900151066248428309 4972811385944581230395077)
                  ·
                    refine ⟨932402134864608980699077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4972811385944581230395077 932402134864608980699077)
                    ·
                      rfl

theorem cell22_2723770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_2723770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2723770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2723770 prefixEnd_2723770 := by exact prefixLift 2723770
  have htrace : WordTrace (prefixWord ++ tailWord_2723770) baseStart_2723770 baseEnd_2723770 := by
    simpa [prefixWord, tailWord_2723770, baseEnd_2723770] using wordTrace_append hprefix tailTrace_2723770
  have hstable : (prefixWord ++ tailWord_2723770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723770).length < 2 ^ (prefixWord ++ tailWord_2723770).sum := by decide
  have hdescent : baseEnd_2723770 < baseStart_2723770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723802 : List Nat := [3, 1, 1, 2, 5, 2, 8]
def baseStart_2723802 : Nat := 118140960795 + 2723802 * 2 ^ 59
def prefixEnd_2723802 : Nat := 4983230072969 + 3 ^ 40 * 2723802 * 2
def baseEnd_2723802 : Nat := 34533818115502650514777

theorem tailTrace_2723802 : CollatzResearch.WordTrace tailWord_2723802 prefixEnd_2723802 34533818115502650514777 := by
  unfold tailWord_2723802
  simp only [CollatzResearch.WordTrace]
  refine ⟨24836305119534504297793415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66230146985425344794115773 24836305119534504297793415)
  ·
    refine ⟨37254457679301756446690123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24836305119534504297793415 37254457679301756446690123)
    ·
      refine ⟨55881686518952634670035185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37254457679301756446690123 55881686518952634670035185)
      ·
        refine ⟨41911264889214476002526389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55881686518952634670035185 41911264889214476002526389)
        ·
          refine ⟨3929181083363857125236849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41911264889214476002526389 3929181083363857125236849)
          ·
            refine ⟨2946885812522892843927637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3929181083363857125236849 2946885812522892843927637)
            ·
              refine ⟨34533818115502650514777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2946885812522892843927637 34533818115502650514777)
              ·
                rfl

theorem cell22_2723802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 8].length) (baseStart_2723802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2723802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2723802 prefixEnd_2723802 := by exact prefixLift 2723802
  have htrace : WordTrace (prefixWord ++ tailWord_2723802) baseStart_2723802 baseEnd_2723802 := by
    simpa [prefixWord, tailWord_2723802, baseEnd_2723802] using wordTrace_append hprefix tailTrace_2723802
  have hstable : (prefixWord ++ tailWord_2723802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723802).length < 2 ^ (prefixWord ++ tailWord_2723802).sum := by decide
  have hdescent : baseEnd_2723802 < baseStart_2723802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723868 : List Nat := [2, 2, 3, 1, 3, 1, 4, 2, 1, 3]
def baseStart_2723868 : Nat := 118140960795 + 2723868 * 2 ^ 59
def prefixEnd_2723868 : Nat := 4983230072969 + 3 ^ 40 * 2723868 * 2
def baseEnd_2723868 : Nat := 932435682267369391748777

theorem tailTrace_2723868 : CollatzResearch.WordTrace tailWord_2723868 prefixEnd_2723868 932435682267369391748777 := by
  unfold tailWord_2723868
  simp only [CollatzResearch.WordTrace]
  refine ⟨49673813847949455231538129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66231751797265940308717505 49673813847949455231538129)
  ·
    refine ⟨37255360385962091423653597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49673813847949455231538129 37255360385962091423653597)
    ·
      refine ⟨13970760144735784283870099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37255360385962091423653597 13970760144735784283870099)
      ·
        refine ⟨20956140217103676425805149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13970760144735784283870099 20956140217103676425805149)
        ·
          refine ⟨7858552581413878659676931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20956140217103676425805149 7858552581413878659676931)
          ·
            refine ⟨11787828872120817989515397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7858552581413878659676931 11787828872120817989515397)
            ·
              refine ⟨2210217913522653373034137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11787828872120817989515397 2210217913522653373034137)
              ·
                refine ⟨1657663435141990029775603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2210217913522653373034137 1657663435141990029775603)
                ·
                  refine ⟨2486495152712985044663405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1657663435141990029775603 2486495152712985044663405)
                  ·
                    refine ⟨932435682267369391748777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2486495152712985044663405 932435682267369391748777)
                    ·
                      rfl

theorem cell22_2723868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_2723868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2723868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2723868 prefixEnd_2723868 := by exact prefixLift 2723868
  have htrace : WordTrace (prefixWord ++ tailWord_2723868) baseStart_2723868 baseEnd_2723868 := by
    simpa [prefixWord, tailWord_2723868, baseEnd_2723868] using wordTrace_append hprefix tailTrace_2723868
  have hstable : (prefixWord ++ tailWord_2723868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723868).length < 2 ^ (prefixWord ++ tailWord_2723868).sum := by decide
  have hdescent : baseEnd_2723868 < baseStart_2723868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723877 : List Nat := [1, 3, 1, 2, 2, 3, 1, 2, 3, 4]
def baseStart_2723877 : Nat := 118140960795 + 2723877 * 2 ^ 59
def prefixEnd_2723877 : Nat := 4983230072969 + 3 ^ 40 * 2723877 * 2
def baseEnd_2723877 : Nat := 932438763151296368273749

theorem tailTrace_2723877 : CollatzResearch.WordTrace tailWord_2723877 prefixEnd_2723877 932438763151296368273749 := by
  unfold tailWord_2723877
  simp only [CollatzResearch.WordTrace]
  refine ⟨99347955952866305000153885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66231970635244203333435923 99347955952866305000153885)
  ·
    refine ⟨37255483482324864375057707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99347955952866305000153885 37255483482324864375057707)
    ·
      refine ⟨55883225223487296562586561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37255483482324864375057707 55883225223487296562586561)
      ·
        refine ⟨41912418917615472421939921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55883225223487296562586561 41912418917615472421939921)
        ·
          refine ⟨31434314188211604316454941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41912418917615472421939921 31434314188211604316454941)
          ·
            refine ⟨11787867820579351618670603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31434314188211604316454941 11787867820579351618670603)
            ·
              refine ⟨17681801730869027428005905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11787867820579351618670603 17681801730869027428005905)
              ·
                refine ⟨13261351298151770571004429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17681801730869027428005905 13261351298151770571004429)
                ·
                  refine ⟨4973006736806913964126661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13261351298151770571004429 4973006736806913964126661)
                  ·
                    refine ⟨932438763151296368273749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4973006736806913964126661 932438763151296368273749)
                    ·
                      rfl

theorem cell22_2723877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_2723877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2723877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2723877 prefixEnd_2723877 := by exact prefixLift 2723877
  have htrace : WordTrace (prefixWord ++ tailWord_2723877) baseStart_2723877 baseEnd_2723877 := by
    simpa [prefixWord, tailWord_2723877, baseEnd_2723877] using wordTrace_append hprefix tailTrace_2723877
  have hstable : (prefixWord ++ tailWord_2723877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723877).length < 2 ^ (prefixWord ++ tailWord_2723877).sum := by decide
  have hdescent : baseEnd_2723877 < baseStart_2723877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723894 : List Nat := [5, 1, 2, 1, 1, 1, 1, 3, 3, 4]
def baseStart_2723894 : Nat := 118140960795 + 2723894 * 2 ^ 59
def prefixEnd_2723894 : Nat := 4983230072969 + 3 ^ 40 * 2723894 * 2
def baseEnd_2723894 : Nat := 932444582598713990598697

theorem tailTrace_2723894 : CollatzResearch.WordTrace tailWord_2723894 prefixEnd_2723894 932444582598713990598697 := by
  unfold tailWord_2723894
  simp only [CollatzResearch.WordTrace]
  refine ⟨6209285999612794806470171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66232383995869811269015157 6209285999612794806470171)
  ·
    refine ⟨9313928999419192209705257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6209285999612794806470171 9313928999419192209705257)
    ·
      refine ⟨6985446749564394157278943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9313928999419192209705257 6985446749564394157278943)
      ·
        refine ⟨10478170124346591235918415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6985446749564394157278943 10478170124346591235918415)
        ·
          refine ⟨15717255186519886853877623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10478170124346591235918415 15717255186519886853877623)
          ·
            refine ⟨23575882779779830280816435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15717255186519886853877623 23575882779779830280816435)
            ·
              refine ⟨35363824169669745421224653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23575882779779830280816435 35363824169669745421224653)
              ·
                refine ⟨13261434063626154532959245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35363824169669745421224653 13261434063626154532959245)
                ·
                  refine ⟨4973037773859807949859717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13261434063626154532959245 4973037773859807949859717)
                  ·
                    refine ⟨932444582598713990598697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4973037773859807949859717 932444582598713990598697)
                    ·
                      rfl

theorem cell22_2723894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_2723894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2723894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2723894 prefixEnd_2723894 := by exact prefixLift 2723894
  have htrace : WordTrace (prefixWord ++ tailWord_2723894) baseStart_2723894 baseEnd_2723894 := by
    simpa [prefixWord, tailWord_2723894, baseEnd_2723894] using wordTrace_append hprefix tailTrace_2723894
  have hstable : (prefixWord ++ tailWord_2723894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723894).length < 2 ^ (prefixWord ++ tailWord_2723894).sum := by decide
  have hdescent : baseEnd_2723894 < baseStart_2723894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723926 : List Nat := [5, 2, 2, 1, 1, 1, 1, 3, 6]
def baseStart_2723926 : Nat := 118140960795 + 2723926 * 2 ^ 59
def prefixEnd_2723926 : Nat := 4983230072969 + 3 ^ 40 * 2723926 * 2
def baseEnd_2723926 : Nat := 310818512284225524599533

theorem tailTrace_2723926 : CollatzResearch.WordTrace tailWord_2723926 prefixEnd_2723926 310818512284225524599533 := by
  unfold tailWord_2723926
  simp only [CollatzResearch.WordTrace]
  refine ⟨6209358945605549148042977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66233162086459190912458421 6209358945605549148042977)
  ·
    refine ⟨4657019209204161861032233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6209358945605549148042977 4657019209204161861032233)
    ·
      refine ⟨3492764406903121395774175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4657019209204161861032233 3492764406903121395774175)
      ·
        refine ⟨5239146610354682093661263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3492764406903121395774175 5239146610354682093661263)
        ·
          refine ⟨7858719915532023140491895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5239146610354682093661263 7858719915532023140491895)
          ·
            refine ⟨11788079873298034710737843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7858719915532023140491895 11788079873298034710737843)
            ·
              refine ⟨17682119809947052066106765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11788079873298034710737843 17682119809947052066106765)
              ·
                refine ⟨6630794928730144524790037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17682119809947052066106765 6630794928730144524790037)
                ·
                  refine ⟨310818512284225524599533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6630794928730144524790037 310818512284225524599533)
                  ·
                    rfl

theorem cell22_2723926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_2723926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2723926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2723926 prefixEnd_2723926 := by exact prefixLift 2723926
  have htrace : WordTrace (prefixWord ++ tailWord_2723926) baseStart_2723926 baseEnd_2723926 := by
    simpa [prefixWord, tailWord_2723926, baseEnd_2723926] using wordTrace_append hprefix tailTrace_2723926
  have hstable : (prefixWord ++ tailWord_2723926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723926).length < 2 ^ (prefixWord ++ tailWord_2723926).sum := by decide
  have hdescent : baseEnd_2723926 < baseStart_2723926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723954 : List Nat := [3, 2, 1, 2, 2, 2, 4, 6]
def baseStart_2723954 : Nat := 118140960795 + 2723954 * 2 ^ 59
def prefixEnd_2723954 : Nat := 4983230072969 + 3 ^ 40 * 2723954 * 2
def baseEnd_2723954 : Nat := 103607235758321537122057

theorem tailTrace_2723954 : CollatzResearch.WordTrace tailWord_2723954 prefixEnd_2723954 103607235758321537122057 := by
  unfold tailWord_2723954
  simp only [CollatzResearch.WordTrace]
  refine ⟨24837691093396836787676729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66233842915724898100471277 24837691093396836787676729)
  ·
    refine ⟨18628268320047627590757547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24837691093396836787676729 18628268320047627590757547)
    ·
      refine ⟨27942402480071441386136321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18628268320047627590757547 27942402480071441386136321)
      ·
        refine ⟨20956801860053581039602241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27942402480071441386136321 20956801860053581039602241)
        ·
          refine ⟨15717601395040185779701681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20956801860053581039602241 15717601395040185779701681)
          ·
            refine ⟨11788201046280139334776261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15717601395040185779701681 11788201046280139334776261)
            ·
              refine ⟨2210287696177526125270549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11788201046280139334776261 2210287696177526125270549)
              ·
                refine ⟨103607235758321537122057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2210287696177526125270549 103607235758321537122057)
                ·
                  rfl

theorem cell22_2723954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 6].length) (baseStart_2723954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2723954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2723954 prefixEnd_2723954 := by exact prefixLift 2723954
  have htrace : WordTrace (prefixWord ++ tailWord_2723954) baseStart_2723954 baseEnd_2723954 := by
    simpa [prefixWord, tailWord_2723954, baseEnd_2723954] using wordTrace_append hprefix tailTrace_2723954
  have hstable : (prefixWord ++ tailWord_2723954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723954).length < 2 ^ (prefixWord ++ tailWord_2723954).sum := by decide
  have hdescent : baseEnd_2723954 < baseStart_2723954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724033 : List Nat := [1, 2, 6, 1, 2, 1, 2, 2, 5]
def baseStart_2724033 : Nat := 118140960795 + 2724033 * 2 ^ 59
def prefixEnd_2724033 : Nat := 4983230072969 + 3 ^ 40 * 2724033 * 2
def baseEnd_2724033 : Nat := 310830721713121320457757

theorem tailTrace_2724033 : CollatzResearch.WordTrace tailWord_2724033 prefixEnd_2724033 310830721713121320457757 := by
  unfold tailWord_2724033
  simp only [CollatzResearch.WordTrace]
  refine ⟨99353645740301143642832753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66235763826867429095221835 99353645740301143642832753)
  ·
    refine ⟨74515234305225857732124565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99353645740301143642832753 74515234305225857732124565)
    ·
      refine ⟨3492901608057462081193339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 74515234305225857732124565 3492901608057462081193339)
      ·
        refine ⟨5239352412086193121790009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3492901608057462081193339 5239352412086193121790009)
        ·
          refine ⟨3929514309064644841342507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5239352412086193121790009 3929514309064644841342507)
          ·
            refine ⟨5894271463596967262013761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3929514309064644841342507 5894271463596967262013761)
            ·
              refine ⟨4420703597697725446510321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5894271463596967262013761 4420703597697725446510321)
              ·
                refine ⟨3315527698273294084882741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4420703597697725446510321 3315527698273294084882741)
                ·
                  refine ⟨310830721713121320457757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3315527698273294084882741 310830721713121320457757)
                  ·
                    rfl

theorem cell22_2724033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 5].length) (baseStart_2724033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724033 prefixEnd_2724033 := by exact prefixLift 2724033
  have htrace : WordTrace (prefixWord ++ tailWord_2724033) baseStart_2724033 baseEnd_2724033 := by
    simpa [prefixWord, tailWord_2724033, baseEnd_2724033] using wordTrace_append hprefix tailTrace_2724033
  have hstable : (prefixWord ++ tailWord_2724033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724033).length < 2 ^ (prefixWord ++ tailWord_2724033).sum := by decide
  have hdescent : baseEnd_2724033 < baseStart_2724033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724061 : List Nat := [1, 4, 3, 2, 1, 2, 1, 2, 6]
def baseStart_2724061 : Nat := 118140960795 + 2724061 * 2 ^ 59
def prefixEnd_2724061 : Nat := 4983230072969 + 3 ^ 40 * 2724061 * 2
def baseEnd_2724061 : Nat := 310833916703860407224395

theorem tailTrace_2724061 : CollatzResearch.WordTrace tailWord_2724061 prefixEnd_2724061 310833916703860407224395 := by
  unfold tailWord_2724061
  simp only [CollatzResearch.WordTrace]
  refine ⟨99354666984199704424852037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66236444656133136283234691 99354666984199704424852037)
  ·
    refine ⟨18629000059537444579659757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99354666984199704424852037 18629000059537444579659757)
    ·
      refine ⟨6985875022326541717372409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18629000059537444579659757 6985875022326541717372409)
      ·
        refine ⟨5239406266744906288029307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6985875022326541717372409 5239406266744906288029307)
        ·
          refine ⟨7859109400117359432043961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5239406266744906288029307 7859109400117359432043961)
          ·
            refine ⟨5894332050088019574032971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7859109400117359432043961 5894332050088019574032971)
            ·
              refine ⟨8841498075132029361049457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5894332050088019574032971 8841498075132029361049457)
              ·
                refine ⟨6631123556349022020787093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8841498075132029361049457 6631123556349022020787093)
                ·
                  refine ⟨310833916703860407224395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6631123556349022020787093 310833916703860407224395)
                  ·
                    rfl

theorem cell22_2724061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_2724061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724061 prefixEnd_2724061 := by exact prefixLift 2724061
  have htrace : WordTrace (prefixWord ++ tailWord_2724061) baseStart_2724061 baseEnd_2724061 := by
    simpa [prefixWord, tailWord_2724061, baseEnd_2724061] using wordTrace_append hprefix tailTrace_2724061
  have hstable : (prefixWord ++ tailWord_2724061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724061).length < 2 ^ (prefixWord ++ tailWord_2724061).sum := by decide
  have hdescent : baseEnd_2724061 < baseStart_2724061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724074 : List Nat := [3, 1, 3, 1, 1, 2, 3, 1, 1, 6]
def baseStart_2724074 : Nat := 118140960795 + 2724074 * 2 ^ 59
def prefixEnd_2724074 : Nat := 4983230072969 + 3 ^ 40 * 2724074 * 2
def baseEnd_2724074 : Nat := 932506200277253521098145

theorem tailTrace_2724074 : CollatzResearch.WordTrace tailWord_2724074 prefixEnd_2724074 932506200277253521098145 := by
  unfold tailWord_2724074
  simp only [CollatzResearch.WordTrace]
  refine ⟨24838785283288151911268819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66236760755435071763383517 24838785283288151911268819)
  ·
    refine ⟨37258177924932227866903229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24838785283288151911268819 37258177924932227866903229)
    ·
      refine ⟨13971816721849585450088711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37258177924932227866903229 13971816721849585450088711)
      ·
        refine ⟨20957725082774378175133067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13971816721849585450088711 20957725082774378175133067)
        ·
          refine ⟨31436587624161567262699601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20957725082774378175133067 31436587624161567262699601)
          ·
            refine ⟨23577440718121175447024701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31436587624161567262699601 23577440718121175447024701)
            ·
              refine ⟨8841540269295440792634263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23577440718121175447024701 8841540269295440792634263)
              ·
                refine ⟨13262310403943161188951395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8841540269295440792634263 13262310403943161188951395)
                ·
                  refine ⟨19893465605914741783427093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13262310403943161188951395 19893465605914741783427093)
                  ·
                    refine ⟨932506200277253521098145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19893465605914741783427093 932506200277253521098145)
                    ·
                      rfl

theorem cell22_2724074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_2724074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724074 prefixEnd_2724074 := by exact prefixLift 2724074
  have htrace : WordTrace (prefixWord ++ tailWord_2724074) baseStart_2724074 baseEnd_2724074 := by
    simpa [prefixWord, tailWord_2724074, baseEnd_2724074] using wordTrace_append hprefix tailTrace_2724074
  have hstable : (prefixWord ++ tailWord_2724074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724074).length < 2 ^ (prefixWord ++ tailWord_2724074).sum := by decide
  have hdescent : baseEnd_2724074 < baseStart_2724074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724209 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 3, 6]
def baseStart_2724209 : Nat := 118140960795 + 2724209 * 2 ^ 59
def prefixEnd_2724209 : Nat := 4983230072969 + 3 ^ 40 * 2724209 * 2
def baseEnd_2724209 : Nat := 932552413536158168972731

theorem tailTrace_2724209 : CollatzResearch.WordTrace tailWord_2724209 prefixEnd_2724209 932552413536158168972731 := by
  unfold tailWord_2724209
  simp only [CollatzResearch.WordTrace]
  refine ⟨99360064987663525701239681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66240043325109017134159787 99360064987663525701239681)
  ·
    refine ⟨74520048740747644275929761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99360064987663525701239681 74520048740747644275929761)
    ·
      refine ⟨55890036555560733206947321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74520048740747644275929761 55890036555560733206947321)
      ·
        refine ⟨41917527416670549905210491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55890036555560733206947321 41917527416670549905210491)
        ·
          refine ⟨62876291125005824857815737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41917527416670549905210491 62876291125005824857815737)
          ·
            refine ⟨47157218343754368643361803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62876291125005824857815737 47157218343754368643361803)
            ·
              refine ⟨70735827515631552965042705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47157218343754368643361803 70735827515631552965042705)
              ·
                refine ⟨53051870636723664723782029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70735827515631552965042705 53051870636723664723782029)
                ·
                  refine ⟨19894451488771374271418261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53051870636723664723782029 19894451488771374271418261)
                  ·
                    refine ⟨932552413536158168972731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19894451488771374271418261 932552413536158168972731)
                    ·
                      rfl

theorem cell22_2724209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_2724209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724209 prefixEnd_2724209 := by exact prefixLift 2724209
  have htrace : WordTrace (prefixWord ++ tailWord_2724209) baseStart_2724209 baseEnd_2724209 := by
    simpa [prefixWord, tailWord_2724209, baseEnd_2724209] using wordTrace_append hprefix tailTrace_2724209
  have hstable : (prefixWord ++ tailWord_2724209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724209).length < 2 ^ (prefixWord ++ tailWord_2724209).sum := by decide
  have hdescent : baseEnd_2724209 < baseStart_2724209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724228 : List Nat := [2, 3, 2, 1, 1, 2, 1, 5, 2, 3]
def baseStart_2724228 : Nat := 118140960795 + 2724228 * 2 ^ 59
def prefixEnd_2724228 : Nat := 4983230072969 + 3 ^ 40 * 2724228 * 2
def baseEnd_2724228 : Nat := 932558917624448452747673

theorem tailTrace_2724228 : CollatzResearch.WordTrace tailWord_2724228 prefixEnd_2724228 932558917624448452747673 := by
  unfold tailWord_2724228
  simp only [CollatzResearch.WordTrace]
  refine ⟨49680378987297345973090669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66240505316396461297454225 49680378987297345973090669)
  ·
    refine ⟨18630142120236504739909001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49680378987297345973090669 18630142120236504739909001)
    ·
      refine ⟨13972606590177378554931751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18630142120236504739909001 13972606590177378554931751)
      ·
        refine ⟨20958909885266067832397627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13972606590177378554931751 20958909885266067832397627)
        ·
          refine ⟨31438364827899101748596441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20958909885266067832397627 31438364827899101748596441)
          ·
            refine ⟨23578773620924326311447331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31438364827899101748596441 23578773620924326311447331)
            ·
              refine ⟨35368160431386489467170997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23578773620924326311447331 35368160431386489467170997)
              ·
                refine ⟨3315765040442483387547281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35368160431386489467170997 3315765040442483387547281)
                ·
                  refine ⟨2486823780331862540660461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3315765040442483387547281 2486823780331862540660461)
                  ·
                    refine ⟨932558917624448452747673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2486823780331862540660461 932558917624448452747673)
                    ·
                      rfl

theorem cell22_2724228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_2724228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724228 prefixEnd_2724228 := by exact prefixLift 2724228
  have htrace : WordTrace (prefixWord ++ tailWord_2724228) baseStart_2724228 baseEnd_2724228 := by
    simpa [prefixWord, tailWord_2724228, baseEnd_2724228] using wordTrace_append hprefix tailTrace_2724228
  have hstable : (prefixWord ++ tailWord_2724228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724228).length < 2 ^ (prefixWord ++ tailWord_2724228).sum := by decide
  have hdescent : baseEnd_2724228 < baseStart_2724228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724273 : List Nat := [1, 2, 2, 4, 1, 2, 1, 3, 3, 3]
def baseStart_2724273 : Nat := 118140960795 + 2724273 * 2 ^ 59
def prefixEnd_2724273 : Nat := 4983230072969 + 3 ^ 40 * 2724273 * 2
def baseEnd_2724273 : Nat := 932574322044083335372535

theorem tailTrace_2724273 : CollatzResearch.WordTrace tailWord_2724273 prefixEnd_2724273 932574322044083335372535 := by
  unfold tailWord_2724273
  simp only [CollatzResearch.WordTrace]
  refine ⟨99362399259431664631569473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66241599506287776421046315 99362399259431664631569473)
  ·
    refine ⟨74521799444573748473677105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99362399259431664631569473 74521799444573748473677105)
    ·
      refine ⟨55891349583430311355257829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74521799444573748473677105 55891349583430311355257829)
      ·
        refine ⟨10479628046893183379110843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55891349583430311355257829 10479628046893183379110843)
        ·
          refine ⟨15719442070339775068666265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10479628046893183379110843 15719442070339775068666265)
          ·
            refine ⟨11789581552754831301499699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15719442070339775068666265 11789581552754831301499699)
            ·
              refine ⟨17684372329132246952249549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11789581552754831301499699 17684372329132246952249549)
              ·
                refine ⟨6631639623424592607093581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17684372329132246952249549 6631639623424592607093581)
                ·
                  refine ⟨2486864858784222227660093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6631639623424592607093581 2486864858784222227660093)
                  ·
                    refine ⟨932574322044083335372535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2486864858784222227660093 932574322044083335372535)
                    ·
                      rfl

theorem cell22_2724273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 3, 3].length) (baseStart_2724273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724273 prefixEnd_2724273 := by exact prefixLift 2724273
  have htrace : WordTrace (prefixWord ++ tailWord_2724273) baseStart_2724273 baseEnd_2724273 := by
    simpa [prefixWord, tailWord_2724273, baseEnd_2724273] using wordTrace_append hprefix tailTrace_2724273
  have hstable : (prefixWord ++ tailWord_2724273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724273).length < 2 ^ (prefixWord ++ tailWord_2724273).sum := by decide
  have hdescent : baseEnd_2724273 < baseStart_2724273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724292 : List Nat := [2, 3, 3, 2, 3, 1, 2, 6]
def baseStart_2724292 : Nat := 118140960795 + 2724292 * 2 ^ 59
def prefixEnd_2724292 : Nat := 4983230072969 + 3 ^ 40 * 2724292 * 2
def baseEnd_2724292 : Nat := 103620091792485957683053

theorem tailTrace_2724292 : CollatzResearch.WordTrace tailWord_2724292 prefixEnd_2724292 103620091792485957683053 := by
  unfold tailWord_2724292
  simp only [CollatzResearch.WordTrace]
  refine ⟨49681546123181415438255565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66242061497575220584340753 49681546123181415438255565)
  ·
    refine ⟨18630579796193030789345837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49681546123181415438255565 18630579796193030789345837)
    ·
      refine ⟨6986467423572386546004689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18630579796193030789345837 6986467423572386546004689)
      ·
        refine ⟨5239850567679289909503517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6986467423572386546004689 5239850567679289909503517)
        ·
          refine ⟨1964943962879733716063819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5239850567679289909503517 1964943962879733716063819)
          ·
            refine ⟨2947415944319600574095729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1964943962879733716063819 2947415944319600574095729)
            ·
              refine ⟨2210561958239700430571797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2947415944319600574095729 2210561958239700430571797)
              ·
                refine ⟨103620091792485957683053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2210561958239700430571797 103620091792485957683053)
                ·
                  rfl

theorem cell22_2724292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 6].length) (baseStart_2724292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724292 prefixEnd_2724292 := by exact prefixLift 2724292
  have htrace : WordTrace (prefixWord ++ tailWord_2724292) baseStart_2724292 baseEnd_2724292 := by
    simpa [prefixWord, tailWord_2724292, baseEnd_2724292] using wordTrace_append hprefix tailTrace_2724292
  have hstable : (prefixWord ++ tailWord_2724292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724292).length < 2 ^ (prefixWord ++ tailWord_2724292).sum := by decide
  have hdescent : baseEnd_2724292 < baseStart_2724292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724363 : List Nat := [1, 1, 1, 1, 7, 2, 1, 2, 1, 5]
def baseStart_2724363 : Nat := 118140960795 + 2724363 * 2 ^ 59
def prefixEnd_2724363 : Nat := 4983230072969 + 3 ^ 40 * 2724363 * 2
def baseEnd_2724363 : Nat := 932605130883353100622259

theorem tailTrace_2724363 : CollatzResearch.WordTrace tailWord_2724363 prefixEnd_2724363 932605130883353100622259 := by
  unfold tailWord_2724363
  simp only [CollatzResearch.WordTrace]
  refine ⟨99365681829105610002345743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66243787886070406668230495 99365681829105610002345743)
  ·
    refine ⟨149048522743658415003518615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99365681829105610002345743 149048522743658415003518615)
    ·
      refine ⟨223572784115487622505277923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149048522743658415003518615 223572784115487622505277923)
      ·
        refine ⟨335359176173231433757916885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223572784115487622505277923 335359176173231433757916885)
        ·
          refine ⟨7859980691560111728701177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 335359176173231433757916885 7859980691560111728701177)
          ·
            refine ⟨5894985518670083796525883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7859980691560111728701177 5894985518670083796525883)
            ·
              refine ⟨8842478278005125694788825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5894985518670083796525883 8842478278005125694788825)
              ·
                refine ⟨6631858708503844271091619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8842478278005125694788825 6631858708503844271091619)
                ·
                  refine ⟨9947788062755766406637429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6631858708503844271091619 9947788062755766406637429)
                  ·
                    refine ⟨932605130883353100622259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9947788062755766406637429 932605130883353100622259)
                    ·
                      rfl

theorem cell22_2724363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 5].length) (baseStart_2724363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724363 prefixEnd_2724363 := by exact prefixLift 2724363
  have htrace : WordTrace (prefixWord ++ tailWord_2724363) baseStart_2724363 baseEnd_2724363 := by
    simpa [prefixWord, tailWord_2724363, baseEnd_2724363] using wordTrace_append hprefix tailTrace_2724363
  have hstable : (prefixWord ++ tailWord_2724363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724363).length < 2 ^ (prefixWord ++ tailWord_2724363).sum := by decide
  have hdescent : baseEnd_2724363 < baseStart_2724363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724376 : List Nat := [2, 1, 2, 3, 3, 11]
def baseStart_2724376 : Nat := 118140960795 + 2724376 * 2 ^ 59
def prefixEnd_2724376 : Nat := 4983230072969 + 3 ^ 40 * 2724376 * 2
def baseEnd_2724376 : Nat := 11513698531469449383299

theorem tailTrace_2724376 : CollatzResearch.WordTrace tailWord_2724376 prefixEnd_2724376 11513698531469449383299 := by
  unfold tailWord_2724376
  simp only [CollatzResearch.WordTrace]
  refine ⟨49683077989029256611284491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66244103985372342148379321 49683077989029256611284491)
  ·
    refine ⟨74524616983543884916926737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49683077989029256611284491 74524616983543884916926737)
    ·
      refine ⟨55893462737657913687695053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74524616983543884916926737 55893462737657913687695053)
      ·
        refine ⟨20960048526621717632885645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55893462737657913687695053 20960048526621717632885645)
        ·
          refine ⟨7860018197483144112332117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20960048526621717632885645 7860018197483144112332117)
          ·
            refine ⟨11513698531469449383299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7860018197483144112332117 11513698531469449383299)
            ·
              rfl

theorem cell22_2724376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 11].length) (baseStart_2724376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724376 prefixEnd_2724376 := by exact prefixLift 2724376
  have htrace : WordTrace (prefixWord ++ tailWord_2724376) baseStart_2724376 baseEnd_2724376 := by
    simpa [prefixWord, tailWord_2724376, baseEnd_2724376] using wordTrace_append hprefix tailTrace_2724376
  have hstable : (prefixWord ++ tailWord_2724376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724376).length < 2 ^ (prefixWord ++ tailWord_2724376).sum := by decide
  have hdescent : baseEnd_2724376 < baseStart_2724376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724378 : List Nat := [3, 1, 1, 3, 1, 1, 4, 2, 2, 4]
def baseStart_2724378 : Nat := 118140960795 + 2724378 * 2 ^ 59
def prefixEnd_2724378 : Nat := 4983230072969 + 3 ^ 40 * 2724378 * 2
def baseEnd_2724378 : Nat := 932610265689898061497213

theorem tailTrace_2724378 : CollatzResearch.WordTrace tailWord_2724378 prefixEnd_2724378 932610265689898061497213 := by
  unfold tailWord_2724378
  simp only [CollatzResearch.WordTrace]
  refine ⟨24841557231012816891035447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66244152616034178376094525 24841557231012816891035447)
  ·
    refine ⟨37262335846519225336553171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24841557231012816891035447 37262335846519225336553171)
    ·
      refine ⟨55893503769778838004829757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37262335846519225336553171 55893503769778838004829757)
      ·
        refine ⟨20960063913667064251811159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55893503769778838004829757 20960063913667064251811159)
        ·
          refine ⟨31440095870500596377716739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20960063913667064251811159 31440095870500596377716739)
          ·
            refine ⟨47160143805750894566575109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31440095870500596377716739 47160143805750894566575109)
            ·
              refine ⟨8842526963578292731232833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47160143805750894566575109 8842526963578292731232833)
              ·
                refine ⟨6631895222683719548424625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8842526963578292731232833 6631895222683719548424625)
                ·
                  refine ⟨4973921417012789661318469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6631895222683719548424625 4973921417012789661318469)
                  ·
                    refine ⟨932610265689898061497213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4973921417012789661318469 932610265689898061497213)
                    ·
                      rfl

theorem cell22_2724378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_2724378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724378 prefixEnd_2724378 := by exact prefixLift 2724378
  have htrace : WordTrace (prefixWord ++ tailWord_2724378) baseStart_2724378 baseEnd_2724378 := by
    simpa [prefixWord, tailWord_2724378, baseEnd_2724378] using wordTrace_append hprefix tailTrace_2724378
  have hstable : (prefixWord ++ tailWord_2724378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724378).length < 2 ^ (prefixWord ++ tailWord_2724378).sum := by decide
  have hdescent : baseEnd_2724378 < baseStart_2724378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724380 : List Nat := [2, 2, 3, 1, 2, 2, 1, 4, 2, 3]
def baseStart_2724380 : Nat := 118140960795 + 2724380 * 2 ^ 59
def prefixEnd_2724380 : Nat := 4983230072969 + 3 ^ 40 * 2724380 * 2
def baseEnd_2724380 : Nat := 932610950330770722947207

theorem tailTrace_2724380 : CollatzResearch.WordTrace tailWord_2724380 prefixEnd_2724380 932610950330770722947207 := by
  unfold tailWord_2724380
  simp only [CollatzResearch.WordTrace]
  refine ⟨49683150935022010952857297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66244201246696014603809729 49683150935022010952857297)
  ·
    refine ⟨37262363201266508214642973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49683150935022010952857297 37262363201266508214642973)
    ·
      refine ⟨13973386200474940580491115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37262363201266508214642973 13973386200474940580491115)
      ·
        refine ⟨20960079300712410870736673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13973386200474940580491115 20960079300712410870736673)
        ·
          refine ⟨15720059475534308153052505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20960079300712410870736673 15720059475534308153052505)
          ·
            refine ⟨11790044606650731114789379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15720059475534308153052505 11790044606650731114789379)
            ·
              refine ⟨17685066909976096672184069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11790044606650731114789379 17685066909976096672184069)
              ·
                refine ⟨3315950045620518126034513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17685066909976096672184069 3315950045620518126034513)
                ·
                  refine ⟨2486962534215388594525885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3315950045620518126034513 2486962534215388594525885)
                  ·
                    refine ⟨932610950330770722947207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2486962534215388594525885 932610950330770722947207)
                    ·
                      rfl

theorem cell22_2724380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_2724380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724380 prefixEnd_2724380 := by exact prefixLift 2724380
  have htrace : WordTrace (prefixWord ++ tailWord_2724380) baseStart_2724380 baseEnd_2724380 := by
    simpa [prefixWord, tailWord_2724380, baseEnd_2724380] using wordTrace_append hprefix tailTrace_2724380
  have hstable : (prefixWord ++ tailWord_2724380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724380).length < 2 ^ (prefixWord ++ tailWord_2724380).sum := by decide
  have hdescent : baseEnd_2724380 < baseStart_2724380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724485 : List Nat := [1, 3, 1, 1, 4, 2, 2, 3, 1, 4]
def baseStart_2724485 : Nat := 118140960795 + 2724485 * 2 ^ 59
def prefixEnd_2724485 : Nat := 4983230072969 + 3 ^ 40 * 2724485 * 2
def baseEnd_2724485 : Nat := 932646893976585449071885

theorem tailTrace_2724485 : CollatzResearch.WordTrace tailWord_2724485 prefixEnd_2724485 932646893976585449071885 := by
  unfold tailWord_2724485
  simp only [CollatzResearch.WordTrace]
  refine ⟨99370131534663624838286909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66246754356442416558857939 99370131534663624838286909)
  ·
    refine ⟨37263799325498859314357591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99370131534663624838286909 37263799325498859314357591)
    ·
      refine ⟨55895698988248288971536387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37263799325498859314357591 55895698988248288971536387)
      ·
        refine ⟨83843548482372433457304581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55895698988248288971536387 83843548482372433457304581)
        ·
          refine ⟨15720665340444831273244609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83843548482372433457304581 15720665340444831273244609)
          ·
            refine ⟨11790499005333623454933457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15720665340444831273244609 11790499005333623454933457)
            ·
              refine ⟨8842874254000217591200093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11790499005333623454933457 8842874254000217591200093)
              ·
                refine ⟨3316077845250081596700035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8842874254000217591200093 3316077845250081596700035)
                ·
                  refine ⟨4974116767875122395050053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3316077845250081596700035 4974116767875122395050053)
                  ·
                    refine ⟨932646893976585449071885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4974116767875122395050053 932646893976585449071885)
                    ·
                      rfl

theorem cell22_2724485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_2724485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724485 prefixEnd_2724485 := by exact prefixLift 2724485
  have htrace : WordTrace (prefixWord ++ tailWord_2724485) baseStart_2724485 baseEnd_2724485 := by
    simpa [prefixWord, tailWord_2724485, baseEnd_2724485] using wordTrace_append hprefix tailTrace_2724485
  have hstable : (prefixWord ++ tailWord_2724485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724485).length < 2 ^ (prefixWord ++ tailWord_2724485).sum := by decide
  have hdescent : baseEnd_2724485 < baseStart_2724485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724506 : List Nat := [3, 1, 1, 6, 2, 1, 2, 1, 5]
def baseStart_2724506 : Nat := 118140960795 + 2724506 * 2 ^ 59
def prefixEnd_2724506 : Nat := 4983230072969 + 3 ^ 40 * 2724506 * 2
def baseEnd_2724506 : Nat := 310884694235249464765607

theorem tailTrace_2724506 : CollatzResearch.WordTrace tailWord_2724506 prefixEnd_2724506 310884694235249464765607 := by
  unfold tailWord_2724506
  simp only [CollatzResearch.WordTrace]
  refine ⟨24842724366896886356200343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66247264978391696949867581 24842724366896886356200343)
  ·
    refine ⟨37264086550345329534300515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24842724366896886356200343 37264086550345329534300515)
    ·
      refine ⟨55896129825517994301450773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37264086550345329534300515 55896129825517994301450773)
      ·
        refine ⟨2620131085571155982880505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 55896129825517994301450773 2620131085571155982880505)
        ·
          refine ⟨1965098314178366987160379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2620131085571155982880505 1965098314178366987160379)
          ·
            refine ⟨2947647471267550480740569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1965098314178366987160379 2947647471267550480740569)
            ·
              refine ⟨2210735603450662860555427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2947647471267550480740569 2210735603450662860555427)
              ·
                refine ⟨3316103405175994290833141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2210735603450662860555427 3316103405175994290833141)
                ·
                  refine ⟨310884694235249464765607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3316103405175994290833141 310884694235249464765607)
                  ·
                    rfl

theorem cell22_2724506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 5].length) (baseStart_2724506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724506 prefixEnd_2724506 := by exact prefixLift 2724506
  have htrace : WordTrace (prefixWord ++ tailWord_2724506) baseStart_2724506 baseEnd_2724506 := by
    simpa [prefixWord, tailWord_2724506, baseEnd_2724506] using wordTrace_append hprefix tailTrace_2724506
  have hstable : (prefixWord ++ tailWord_2724506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724506).length < 2 ^ (prefixWord ++ tailWord_2724506).sum := by decide
  have hdescent : baseEnd_2724506 < baseStart_2724506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724545 : List Nat := [1, 2, 6, 2, 11]
def baseStart_2724545 : Nat := 118140960795 + 2724545 * 2 ^ 59
def prefixEnd_2724545 : Nat := 4983230072969 + 3 ^ 40 * 2724545 * 2
def baseEnd_2724545 : Nat := 3838137585196564990007

theorem tailTrace_2724545 : CollatzResearch.WordTrace tailWord_2724545 prefixEnd_2724545 3838137585196564990007 := by
  unfold tailWord_2724545
  simp only [CollatzResearch.WordTrace]
  refine ⟨99372319914446255085471089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66248213276297503390314059 99372319914446255085471089)
  ·
    refine ⟨74529239935834691314103317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99372319914446255085471089 74529239935834691314103317)
    ·
      refine ⟨3493558121992251155348593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 74529239935834691314103317 3493558121992251155348593)
      ·
        refine ⟨2620168591494188366511445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3493558121992251155348593 2620168591494188366511445)
        ·
          refine ⟨3838137585196564990007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2620168591494188366511445 3838137585196564990007)
          ·
            rfl

theorem cell22_2724545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 11].length) (baseStart_2724545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724545 prefixEnd_2724545 := by exact prefixLift 2724545
  have htrace : WordTrace (prefixWord ++ tailWord_2724545) baseStart_2724545 baseEnd_2724545 := by
    simpa [prefixWord, tailWord_2724545, baseEnd_2724545] using wordTrace_append hprefix tailTrace_2724545
  have hstable : (prefixWord ++ tailWord_2724545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724545).length < 2 ^ (prefixWord ++ tailWord_2724545).sum := by decide
  have hdescent : baseEnd_2724545 < baseStart_2724545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724562 : List Nat := [3, 2, 2, 2, 3, 2, 1, 7]
def baseStart_2724562 : Nat := 118140960795 + 2724562 * 2 ^ 59
def prefixEnd_2724562 : Nat := 4983230072969 + 3 ^ 40 * 2724562 * 2
def baseEnd_2724562 : Nat := 103630361405575879432961

theorem tailTrace_2724562 : CollatzResearch.WordTrace tailWord_2724562 prefixEnd_2724562 103630361405575879432961 := by
  unfold tailWord_2724562
  simp only [CollatzResearch.WordTrace]
  refine ⟨24843234988846166747209985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66248626636923111325893293 24843234988846166747209985)
  ·
    refine ⟨18632426241634625060407489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24843234988846166747209985 18632426241634625060407489)
    ·
      refine ⟨13974319681225968795305617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18632426241634625060407489 13974319681225968795305617)
      ·
        refine ⟨10480739760919476596479213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13974319681225968795305617 10480739760919476596479213)
        ·
          refine ⟨3930277410344803723679705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10480739760919476596479213 3930277410344803723679705)
          ·
            refine ⟨2947708057758602792759779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3930277410344803723679705 2947708057758602792759779)
            ·
              refine ⟨4421562086637904189139669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2947708057758602792759779 4421562086637904189139669)
              ·
                refine ⟨103630361405575879432961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4421562086637904189139669 103630361405575879432961)
                ·
                  rfl

theorem cell22_2724562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 7].length) (baseStart_2724562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724562 prefixEnd_2724562 := by exact prefixLift 2724562
  have htrace : WordTrace (prefixWord ++ tailWord_2724562) baseStart_2724562 baseEnd_2724562 := by
    simpa [prefixWord, tailWord_2724562, baseEnd_2724562] using wordTrace_append hprefix tailTrace_2724562
  have hstable : (prefixWord ++ tailWord_2724562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724562).length < 2 ^ (prefixWord ++ tailWord_2724562).sum := by decide
  have hdescent : baseEnd_2724562 < baseStart_2724562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724577 : List Nat := [1, 2, 3, 1, 4, 2, 1, 2, 3, 3]
def baseStart_2724577 : Nat := 118140960795 + 2724577 * 2 ^ 59
def prefixEnd_2724577 : Nat := 4983230072969 + 3 ^ 40 * 2724577 * 2
def baseEnd_2724577 : Nat := 932678387456727875771603

theorem tailTrace_2724577 : CollatzResearch.WordTrace tailWord_2724577 prefixEnd_2724577 932678387456727875771603 := by
  unfold tailWord_2724577
  simp only [CollatzResearch.WordTrace]
  refine ⟨99373487050330324550635985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66248991366886883033757323 99373487050330324550635985)
  ·
    refine ⟨74530115287747743412976989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99373487050330324550635985 74530115287747743412976989)
    ·
      refine ⟨27948793232905403779866371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74530115287747743412976989 27948793232905403779866371)
      ·
        refine ⟨41923189849358105669799557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27948793232905403779866371 41923189849358105669799557)
        ·
          refine ⟨7860598096754644813087417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41923189849358105669799557 7860598096754644813087417)
          ·
            refine ⟨5895448572565983609815563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7860598096754644813087417 5895448572565983609815563)
            ·
              refine ⟨8843172858848975414723345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5895448572565983609815563 8843172858848975414723345)
              ·
                refine ⟨6632379644136731561042509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8843172858848975414723345 6632379644136731561042509)
                ·
                  refine ⟨2487142366551274335390941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6632379644136731561042509 2487142366551274335390941)
                  ·
                    refine ⟨932678387456727875771603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2487142366551274335390941 932678387456727875771603)
                    ·
                      rfl

theorem cell22_2724577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_2724577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724577 prefixEnd_2724577 := by exact prefixLift 2724577
  have htrace : WordTrace (prefixWord ++ tailWord_2724577) baseStart_2724577 baseEnd_2724577 := by
    simpa [prefixWord, tailWord_2724577, baseEnd_2724577] using wordTrace_append hprefix tailTrace_2724577
  have hstable : (prefixWord ++ tailWord_2724577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724577).length < 2 ^ (prefixWord ++ tailWord_2724577).sum := by decide
  have hdescent : baseEnd_2724577 < baseStart_2724577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724588 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 3, 7]
def baseStart_2724588 : Nat := 118140960795 + 2724588 * 2 ^ 59
def prefixEnd_2724588 : Nat := 4983230072969 + 3 ^ 40 * 2724588 * 2
def baseEnd_2724588 : Nat := 932682152981527513746569

theorem tailTrace_2724588 : CollatzResearch.WordTrace tailWord_2724588 prefixEnd_2724588 932682152981527513746569 := by
  unfold tailWord_2724588
  simp only [CollatzResearch.WordTrace]
  refine ⟨49686944126645236714643209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66249258835526982286190945 49686944126645236714643209)
  ·
    refine ⟨37265208094983927535982407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49686944126645236714643209 37265208094983927535982407)
    ·
      refine ⟨55897812142475891303973611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37265208094983927535982407 55897812142475891303973611)
      ·
        refine ⟨83846718213713836955960417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55897812142475891303973611 83846718213713836955960417)
        ·
          refine ⟨62885038660285377716970313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83846718213713836955960417 62885038660285377716970313)
          ·
            refine ⟨47163778995214033287727735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62885038660285377716970313 47163778995214033287727735)
            ·
              refine ⟨70745668492821049931591603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47163778995214033287727735 70745668492821049931591603)
              ·
                refine ⟨106118502739231574897387405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70745668492821049931591603 106118502739231574897387405)
                ·
                  refine ⟨39794438527211840586520277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106118502739231574897387405 39794438527211840586520277)
                  ·
                    refine ⟨932682152981527513746569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39794438527211840586520277 932682152981527513746569)
                    ·
                      rfl

theorem cell22_2724588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_2724588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724588 prefixEnd_2724588 := by exact prefixLift 2724588
  have htrace : WordTrace (prefixWord ++ tailWord_2724588) baseStart_2724588 baseEnd_2724588 := by
    simpa [prefixWord, tailWord_2724588, baseEnd_2724588] using wordTrace_append hprefix tailTrace_2724588
  have hstable : (prefixWord ++ tailWord_2724588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724588).length < 2 ^ (prefixWord ++ tailWord_2724588).sum := by decide
  have hdescent : baseEnd_2724588 < baseStart_2724588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724594 : List Nat := [3, 2, 1, 3, 1, 2, 1, 5, 1, 3]
def baseStart_2724594 : Nat := 118140960795 + 2724594 * 2 ^ 59
def prefixEnd_2724594 : Nat := 4983230072969 + 3 ^ 40 * 2724594 * 2
def baseEnd_2724594 : Nat := 932684206904145498096551

theorem tailTrace_2724594 : CollatzResearch.WordTrace tailWord_2724594 prefixEnd_2724594 932684206904145498096551 := by
  unfold tailWord_2724594
  simp only [CollatzResearch.WordTrace]
  refine ⟨24843526772817184113501209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66249404727512490969336557 24843526772817184113501209)
  ·
    refine ⟨18632645079612888085125907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24843526772817184113501209 18632645079612888085125907)
    ·
      refine ⟨27948967619419332127688861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18632645079612888085125907 27948967619419332127688861)
      ·
        refine ⟨10480862857282249547883323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27948967619419332127688861 10480862857282249547883323)
        ·
          refine ⟨15721294285923374321824985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10480862857282249547883323 15721294285923374321824985)
          ·
            refine ⟨11790970714442530741368739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15721294285923374321824985 11790970714442530741368739)
            ·
              refine ⟨17686456071663796112053109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11790970714442530741368739 17686456071663796112053109)
              ·
                refine ⟨1658105256718480885504979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17686456071663796112053109 1658105256718480885504979)
                ·
                  refine ⟨2487157885077721328257469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1658105256718480885504979 2487157885077721328257469)
                  ·
                    refine ⟨932684206904145498096551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2487157885077721328257469 932684206904145498096551)
                    ·
                      rfl

theorem cell22_2724594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_2724594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724594 prefixEnd_2724594 := by exact prefixLift 2724594
  have htrace : WordTrace (prefixWord ++ tailWord_2724594) baseStart_2724594 baseEnd_2724594 := by
    simpa [prefixWord, tailWord_2724594, baseEnd_2724594] using wordTrace_append hprefix tailTrace_2724594
  have hstable : (prefixWord ++ tailWord_2724594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724594).length < 2 ^ (prefixWord ++ tailWord_2724594).sum := by decide
  have hdescent : baseEnd_2724594 < baseStart_2724594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724654 : List Nat := [4, 1, 3, 2, 1, 1, 2, 3, 1, 4]
def baseStart_2724654 : Nat := 118140960795 + 2724654 * 2 ^ 59
def prefixEnd_2724654 : Nat := 4983230072969 + 3 ^ 40 * 2724654 * 2
def baseEnd_2724654 : Nat := 932704746130325341596367

theorem tailTrace_2724654 : CollatzResearch.WordTrace tailWord_2724654 prefixEnd_2724654 932704746130325341596367 := by
  unfold tailWord_2724654
  simp only [CollatzResearch.WordTrace]
  refine ⟨12422036933881420837648627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66250863647367577800792677 12422036933881420837648627)
  ·
    refine ⟨18633055400822131256472941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12422036933881420837648627 18633055400822131256472941)
    ·
      refine ⟨6987395775308299221177353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18633055400822131256472941 6987395775308299221177353)
      ·
        refine ⟨5240546831481224415883015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6987395775308299221177353 5240546831481224415883015)
        ·
          refine ⟨7860820247221836623824523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5240546831481224415883015 7860820247221836623824523)
          ·
            refine ⟨11791230370832754935736785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7860820247221836623824523 11791230370832754935736785)
            ·
              refine ⟨8843422778124566201802589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11791230370832754935736785 8843422778124566201802589)
              ·
                refine ⟨3316283541796712325675971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8843422778124566201802589 3316283541796712325675971)
                ·
                  refine ⟨4974425312695068488513957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3316283541796712325675971 4974425312695068488513957)
                  ·
                    refine ⟨932704746130325341596367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4974425312695068488513957 932704746130325341596367)
                    ·
                      rfl

theorem cell22_2724654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_2724654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724654 prefixEnd_2724654 := by exact prefixLift 2724654
  have htrace : WordTrace (prefixWord ++ tailWord_2724654) baseStart_2724654 baseEnd_2724654 := by
    simpa [prefixWord, tailWord_2724654, baseEnd_2724654] using wordTrace_append hprefix tailTrace_2724654
  have hstable : (prefixWord ++ tailWord_2724654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724654).length < 2 ^ (prefixWord ++ tailWord_2724654).sum := by decide
  have hdescent : baseEnd_2724654 < baseStart_2724654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724669 : List Nat := [1, 4, 1, 4, 2, 2, 1, 1, 6]
def baseStart_2724669 : Nat := 118140960795 + 2724669 * 2 ^ 59
def prefixEnd_2724669 : Nat := 4983230072969 + 3 ^ 40 * 2724669 * 2
def baseEnd_2724669 : Nat := 310903293645623434157107

theorem tailTrace_2724669 : CollatzResearch.WordTrace tailWord_2724669 prefixEnd_2724669 310903293645623434157107 := by
  unfold tailWord_2724669
  simp only [CollatzResearch.WordTrace]
  refine ⟨99376842565997024262985061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66251228377331349508656707 99376842565997024262985061)
  ·
    refine ⟨18633157981124442049309699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99376842565997024262985061 18633157981124442049309699)
    ·
      refine ⟨27949736971686663073964549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18633157981124442049309699 27949736971686663073964549)
      ·
        refine ⟨5240575682191249326368353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27949736971686663073964549 5240575682191249326368353)
        ·
          refine ⟨3930431761643436994776265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5240575682191249326368353 3930431761643436994776265)
          ·
            refine ⟨2947823821232577746082199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3930431761643436994776265 2947823821232577746082199)
            ·
              refine ⟨4421735731848866619123299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2947823821232577746082199 4421735731848866619123299)
              ·
                refine ⟨6632603597773299928684949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4421735731848866619123299 6632603597773299928684949)
                ·
                  refine ⟨310903293645623434157107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6632603597773299928684949 310903293645623434157107)
                  ·
                    rfl

theorem cell22_2724669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_2724669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724669 prefixEnd_2724669 := by exact prefixLift 2724669
  have htrace : WordTrace (prefixWord ++ tailWord_2724669) baseStart_2724669 baseEnd_2724669 := by
    simpa [prefixWord, tailWord_2724669, baseEnd_2724669] using wordTrace_append hprefix tailTrace_2724669
  have hstable : (prefixWord ++ tailWord_2724669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724669).length < 2 ^ (prefixWord ++ tailWord_2724669).sum := by decide
  have hdescent : baseEnd_2724669 < baseStart_2724669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724680 : List Nat := [2, 1, 3, 1, 1, 3, 4, 7]
def baseStart_2724680 : Nat := 118140960795 + 2724680 * 2 ^ 59
def prefixEnd_2724680 : Nat := 4983230072969 + 3 ^ 40 * 2724680 * 2
def baseEnd_2724680 : Nat := 103634849606852215605143

theorem tailTrace_2724680 : CollatzResearch.WordTrace tailWord_2724680 prefixEnd_2724680 103634849606852215605143 := by
  unfold tailWord_2724680
  simp only [CollatzResearch.WordTrace]
  refine ⟨49688621884478586570817747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66251495845971448761090329 49688621884478586570817747)
  ·
    refine ⟨74532932826717879856226621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49688621884478586570817747 74532932826717879856226621)
    ·
      refine ⟨27949849810019204946084983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74532932826717879856226621 27949849810019204946084983)
      ·
        refine ⟨41924774715028807419127475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27949849810019204946084983 41924774715028807419127475)
        ·
          refine ⟨62887162072543211128691213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41924774715028807419127475 62887162072543211128691213)
          ·
            refine ⟨23582685777203704173259205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62887162072543211128691213 23582685777203704173259205)
            ·
              refine ⟨4421753583225694532486101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23582685777203704173259205 4421753583225694532486101)
              ·
                refine ⟨103634849606852215605143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4421753583225694532486101 103634849606852215605143)
                ·
                  rfl

theorem cell22_2724680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 7].length) (baseStart_2724680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724680 prefixEnd_2724680 := by exact prefixLift 2724680
  have htrace : WordTrace (prefixWord ++ tailWord_2724680) baseStart_2724680 baseEnd_2724680 := by
    simpa [prefixWord, tailWord_2724680, baseEnd_2724680] using wordTrace_append hprefix tailTrace_2724680
  have hstable : (prefixWord ++ tailWord_2724680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724680).length < 2 ^ (prefixWord ++ tailWord_2724680).sum := by decide
  have hdescent : baseEnd_2724680 < baseStart_2724680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724684 : List Nat := [2, 2, 1, 3, 3, 2, 1, 3, 2, 3]
def baseStart_2724684 : Nat := 118140960795 + 2724684 * 2 ^ 59
def prefixEnd_2724684 : Nat := 4983230072969 + 3 ^ 40 * 2724684 * 2
def baseEnd_2724684 : Nat := 932715015743415263346275

theorem tailTrace_2724684 : CollatzResearch.WordTrace tailWord_2724684 prefixEnd_2724684 932715015743415263346275 := by
  unfold tailWord_2724684
  simp only [CollatzResearch.WordTrace]
  refine ⟨49688694830471340912390553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66251593107295121216520737 49688694830471340912390553)
  ·
    refine ⟨37266521122853505684292915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49688694830471340912390553 37266521122853505684292915)
    ·
      refine ⟨55899781684280258526439373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37266521122853505684292915 55899781684280258526439373)
      ·
        refine ⟨20962418131605096947414765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55899781684280258526439373 20962418131605096947414765)
        ·
          refine ⟨7860906799351911355280537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20962418131605096947414765 7860906799351911355280537)
          ·
            refine ⟨5895680099513933516460403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7860906799351911355280537 5895680099513933516460403)
            ·
              refine ⟨8843520149270900274690605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5895680099513933516460403 8843520149270900274690605)
              ·
                refine ⟨3316320055976587603008977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8843520149270900274690605 3316320055976587603008977)
                ·
                  refine ⟨2487240041982440702256733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3316320055976587603008977 2487240041982440702256733)
                  ·
                    refine ⟨932715015743415263346275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2487240041982440702256733 932715015743415263346275)
                    ·
                      rfl

theorem cell22_2724684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 2, 3].length) (baseStart_2724684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724684 prefixEnd_2724684 := by exact prefixLift 2724684
  have htrace : WordTrace (prefixWord ++ tailWord_2724684) baseStart_2724684 baseEnd_2724684 := by
    simpa [prefixWord, tailWord_2724684, baseEnd_2724684] using wordTrace_append hprefix tailTrace_2724684
  have hstable : (prefixWord ++ tailWord_2724684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724684).length < 2 ^ (prefixWord ++ tailWord_2724684).sum := by decide
  have hdescent : baseEnd_2724684 < baseStart_2724684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724817 : List Nat := [1, 2, 2, 1, 2, 1, 4, 3, 2, 4]
def baseStart_2724817 : Nat := 118140960795 + 2724817 * 2 ^ 59
def prefixEnd_2724817 : Nat := 4983230072969 + 3 ^ 40 * 2724817 * 2
def baseEnd_2724817 : Nat := 932760544361447249770867

theorem tailTrace_2724817 : CollatzResearch.WordTrace tailWord_2724817 prefixEnd_2724817 932760544361447249770867 := by
  unfold tailWord_2724817
  simp only [CollatzResearch.WordTrace]
  refine ⟨99382240569460845539372705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66254827046307230359581803 99382240569460845539372705)
  ·
    refine ⟨74536680427095634154529529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99382240569460845539372705 74536680427095634154529529)
    ·
      refine ⟨55902510320321725615897147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74536680427095634154529529 55902510320321725615897147)
      ·
        refine ⟨83853765480482588423845721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55902510320321725615897147 83853765480482588423845721)
        ·
          refine ⟨62890324110361941317884291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83853765480482588423845721 62890324110361941317884291)
          ·
            refine ⟨94335486165542911976826437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62890324110361941317884291 94335486165542911976826437)
            ·
              refine ⟨17687903656039295995654957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94335486165542911976826437 17687903656039295995654957)
              ·
                refine ⟨6632963871014735998370609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17687903656039295995654957 6632963871014735998370609)
                ·
                  refine ⟨4974722903261051998777957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6632963871014735998370609 4974722903261051998777957)
                  ·
                    refine ⟨932760544361447249770867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4974722903261051998777957 932760544361447249770867)
                    ·
                      rfl

theorem cell22_2724817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_2724817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724817 prefixEnd_2724817 := by exact prefixLift 2724817
  have htrace : WordTrace (prefixWord ++ tailWord_2724817) baseStart_2724817 baseEnd_2724817 := by
    simpa [prefixWord, tailWord_2724817, baseEnd_2724817] using wordTrace_append hprefix tailTrace_2724817
  have hstable : (prefixWord ++ tailWord_2724817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724817).length < 2 ^ (prefixWord ++ tailWord_2724817).sum := by decide
  have hdescent : baseEnd_2724817 < baseStart_2724817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724898 : List Nat := [3, 3, 1, 1, 1, 4, 1, 4, 1, 3]
def baseStart_2724898 : Nat := 118140960795 + 2724898 * 2 ^ 59
def prefixEnd_2724898 : Nat := 4983230072969 + 3 ^ 40 * 2724898 * 2
def baseEnd_2724898 : Nat := 932788272316790038495619

theorem tailTrace_2724898 : CollatzResearch.WordTrace tailWord_2724898 prefixEnd_2724898 932788272316790038495619 := by
  unfold tailWord_2724898
  simp only [CollatzResearch.WordTrace]
  refine ⟨24846298720541849093267837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66256796588111597582047565 24846298720541849093267837)
  ·
    refine ⟨9317362020203193409975439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24846298720541849093267837 9317362020203193409975439)
    ·
      refine ⟨13976043030304790114963159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9317362020203193409975439 13976043030304790114963159)
      ·
        refine ⟨20964064545457185172444739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13976043030304790114963159 20964064545457185172444739)
        ·
          refine ⟨31446096818185777758667109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20964064545457185172444739 31446096818185777758667109)
          ·
            refine ⟨5896143153409833329750083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31446096818185777758667109 5896143153409833329750083)
            ·
              refine ⟨8844214730114749994625125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5896143153409833329750083 8844214730114749994625125)
              ·
                refine ⟨1658290261896515623992211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8844214730114749994625125 1658290261896515623992211)
                ·
                  refine ⟨2487435392844773435988317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1658290261896515623992211 2487435392844773435988317)
                  ·
                    refine ⟨932788272316790038495619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2487435392844773435988317 932788272316790038495619)
                    ·
                      rfl

theorem cell22_2724898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_2724898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724898 prefixEnd_2724898 := by exact prefixLift 2724898
  have htrace : WordTrace (prefixWord ++ tailWord_2724898) baseStart_2724898 baseEnd_2724898 := by
    simpa [prefixWord, tailWord_2724898, baseEnd_2724898] using wordTrace_append hprefix tailTrace_2724898
  have hstable : (prefixWord ++ tailWord_2724898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724898).length < 2 ^ (prefixWord ++ tailWord_2724898).sum := by decide
  have hdescent : baseEnd_2724898 < baseStart_2724898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724907 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 5, 4]
def baseStart_2724907 : Nat := 118140960795 + 2724907 * 2 ^ 59
def prefixEnd_2724907 : Nat := 4983230072969 + 3 ^ 40 * 2724907 * 2
def baseEnd_2724907 : Nat := 932791353200717015020591

theorem tailTrace_2724907 : CollatzResearch.WordTrace tailWord_2724907 prefixEnd_2724907 932791353200717015020591 := by
  unfold tailWord_2724907
  simp only [CollatzResearch.WordTrace]
  refine ⟨99385523139134790910148975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66257015426089860606765983 99385523139134790910148975)
  ·
    refine ⟨149078284708702186365223463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99385523139134790910148975 149078284708702186365223463)
    ·
      refine ⟨223617427063053279547835195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149078284708702186365223463 223617427063053279547835195)
      ·
        refine ⟨335426140594579919321752793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223617427063053279547835195 335426140594579919321752793)
        ·
          refine ⟨251569605445934939491314595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335426140594579919321752793 251569605445934939491314595)
          ·
            refine ⟨377354408168902409236971893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251569605445934939491314595 377354408168902409236971893)
            ·
              refine ⟨35376975765834600865966115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 377354408168902409236971893 35376975765834600865966115)
              ·
                refine ⟨53065463648751901298949173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35376975765834600865966115 53065463648751901298949173)
                ·
                  refine ⟨4974887217070490746776485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53065463648751901298949173 4974887217070490746776485)
                  ·
                    refine ⟨932791353200717015020591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4974887217070490746776485 932791353200717015020591)
                    ·
                      rfl

theorem cell22_2724907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 4].length) (baseStart_2724907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724907 prefixEnd_2724907 := by exact prefixLift 2724907
  have htrace : WordTrace (prefixWord ++ tailWord_2724907) baseStart_2724907 baseEnd_2724907 := by
    simpa [prefixWord, tailWord_2724907, baseEnd_2724907] using wordTrace_append hprefix tailTrace_2724907
  have hstable : (prefixWord ++ tailWord_2724907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724907).length < 2 ^ (prefixWord ++ tailWord_2724907).sum := by decide
  have hdescent : baseEnd_2724907 < baseStart_2724907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724922 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 8]
def baseStart_2724922 : Nat := 118140960795 + 2724922 * 2 ^ 59
def prefixEnd_2724922 : Nat := 4983230072969 + 3 ^ 40 * 2724922 * 2
def baseEnd_2724922 : Nat := 310932162669087325298515

theorem tailTrace_2724922 : CollatzResearch.WordTrace tailWord_2724922 prefixEnd_2724922 310932162669087325298515 := by
  unfold tailWord_2724922
  simp only [CollatzResearch.WordTrace]
  refine ⟨24846517558520112117986255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66257380156053632314630013 24846517558520112117986255)
  ·
    refine ⟨37269776337780168176979383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24846517558520112117986255 37269776337780168176979383)
    ·
      refine ⟨55904664506670252265469075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37269776337780168176979383 55904664506670252265469075)
      ·
        refine ⟨83856996760005378398203613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55904664506670252265469075 83856996760005378398203613)
        ·
          refine ⟨31446373785002016899326355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83856996760005378398203613 31446373785002016899326355)
          ·
            refine ⟨47169560677503025348989533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31446373785002016899326355 47169560677503025348989533)
            ·
              refine ⟨17688585254063634505871075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47169560677503025348989533 17688585254063634505871075)
              ·
                refine ⟨26532877881095451758806613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17688585254063634505871075 26532877881095451758806613)
                ·
                  refine ⟨310932162669087325298515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26532877881095451758806613 310932162669087325298515)
                  ·
                    rfl

theorem cell22_2724922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 8].length) (baseStart_2724922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724922 prefixEnd_2724922 := by exact prefixLift 2724922
  have htrace : WordTrace (prefixWord ++ tailWord_2724922) baseStart_2724922 baseEnd_2724922 := by
    simpa [prefixWord, tailWord_2724922, baseEnd_2724922] using wordTrace_append hprefix tailTrace_2724922
  have hstable : (prefixWord ++ tailWord_2724922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724922).length < 2 ^ (prefixWord ++ tailWord_2724922).sum := by decide
  have hdescent : baseEnd_2724922 < baseStart_2724922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724924 : List Nat := [2, 2, 2, 2, 2, 2, 2, 1, 3, 4]
def baseStart_2724924 : Nat := 118140960795 + 2724924 * 2 ^ 59
def prefixEnd_2724924 : Nat := 4983230072969 + 3 ^ 40 * 2724924 * 2
def baseEnd_2724924 : Nat := 932797172648134637345539

theorem tailTrace_2724924 : CollatzResearch.WordTrace tailWord_2724924 prefixEnd_2724924 932797172648134637345539 := by
  unfold tailWord_2724924
  simp only [CollatzResearch.WordTrace]
  refine ⟨49693071590036601406758913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66257428786715468542345217 49693071590036601406758913)
  ·
    refine ⟨37269803692527451055069185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49693071590036601406758913 37269803692527451055069185)
    ·
      refine ⟨27952352769395588291301889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37269803692527451055069185 27952352769395588291301889)
      ·
        refine ⟨20964264577046691218476417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27952352769395588291301889 20964264577046691218476417)
        ·
          refine ⟨15723198432785018413857313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20964264577046691218476417 15723198432785018413857313)
          ·
            refine ⟨11792398824588763810392985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15723198432785018413857313 11792398824588763810392985)
            ·
              refine ⟨8844299118441572857794739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11792398824588763810392985 8844299118441572857794739)
              ·
                refine ⟨13266448677662359286692109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8844299118441572857794739 13266448677662359286692109)
                ·
                  refine ⟨4974918254123384732509541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13266448677662359286692109 4974918254123384732509541)
                  ·
                    refine ⟨932797172648134637345539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4974918254123384732509541 932797172648134637345539)
                    ·
                      rfl

theorem cell22_2724924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_2724924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724924 prefixEnd_2724924 := by exact prefixLift 2724924
  have htrace : WordTrace (prefixWord ++ tailWord_2724924) baseStart_2724924 baseEnd_2724924 := by
    simpa [prefixWord, tailWord_2724924, baseEnd_2724924] using wordTrace_append hprefix tailTrace_2724924
  have hstable : (prefixWord ++ tailWord_2724924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724924).length < 2 ^ (prefixWord ++ tailWord_2724924).sum := by decide
  have hdescent : baseEnd_2724924 < baseStart_2724924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724937 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 3, 5]
def baseStart_2724937 : Nat := 118140960795 + 2724937 * 2 ^ 59
def prefixEnd_2724937 : Nat := 4983230072969 + 3 ^ 40 * 2724937 * 2
def baseEnd_2724937 : Nat := 932801622813806936770499

theorem tailTrace_2724937 : CollatzResearch.WordTrace tailWord_2724937 prefixEnd_2724937 932801622813806936770499 := by
  unfold tailWord_2724937
  simp only [CollatzResearch.WordTrace]
  refine ⟨99386617329026106033741065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66257744886017404022494043 99386617329026106033741065)
  ·
    refine ⟨74539962996769579525305799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99386617329026106033741065 74539962996769579525305799)
    ·
      refine ⟨111809944495154369287958699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74539962996769579525305799 111809944495154369287958699)
      ·
        refine ⟨167714916742731553931938049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111809944495154369287958699 167714916742731553931938049)
        ·
          refine ⟨125786187557048665448953537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167714916742731553931938049 125786187557048665448953537)
          ·
            refine ⟨94339640667786499086715153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125786187557048665448953537 94339640667786499086715153)
            ·
              refine ⟨70754730500839874315036365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94339640667786499086715153 70754730500839874315036365)
              ·
                refine ⟨26533023937814952868138637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70754730500839874315036365 26533023937814952868138637)
                ·
                  refine ⟨9949883976680607325551989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26533023937814952868138637 9949883976680607325551989)
                  ·
                    refine ⟨932801622813806936770499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9949883976680607325551989 932801622813806936770499)
                    ·
                      rfl

theorem cell22_2724937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 5].length) (baseStart_2724937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724937 prefixEnd_2724937 := by exact prefixLift 2724937
  have htrace : WordTrace (prefixWord ++ tailWord_2724937) baseStart_2724937 baseEnd_2724937 := by
    simpa [prefixWord, tailWord_2724937, baseEnd_2724937] using wordTrace_append hprefix tailTrace_2724937
  have hstable : (prefixWord ++ tailWord_2724937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724937).length < 2 ^ (prefixWord ++ tailWord_2724937).sum := by decide
  have hdescent : baseEnd_2724937 < baseStart_2724937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724956 : List Nat := [2, 2, 4, 1, 1, 1, 1, 6, 4]
def baseStart_2724956 : Nat := 118140960795 + 2724956 * 2 ^ 59
def prefixEnd_2724956 : Nat := 4983230072969 + 3 ^ 40 * 2724956 * 2
def baseEnd_2724956 : Nat := 310936042300699073515147

theorem tailTrace_2724956 : CollatzResearch.WordTrace tailWord_2724956 prefixEnd_2724956 310936042300699073515147 := by
  unfold tailWord_2724956
  simp only [CollatzResearch.WordTrace]
  refine ⟨49693655157978636139341361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66258206877304848185788481 49693655157978636139341361)
  ·
    refine ⟨37270241368483977104506021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49693655157978636139341361 37270241368483977104506021)
    ·
      refine ⟨6988170256590745707094879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37270241368483977104506021 6988170256590745707094879)
      ·
        refine ⟨10482255384886118560642319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6988170256590745707094879 10482255384886118560642319)
        ·
          refine ⟨15723383077329177840963479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10482255384886118560642319 15723383077329177840963479)
          ·
            refine ⟨23585074615993766761445219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15723383077329177840963479 23585074615993766761445219)
            ·
              refine ⟨35377611923990650142167829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23585074615993766761445219 35377611923990650142167829)
              ·
                refine ⟨1658325558937061725414117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35377611923990650142167829 1658325558937061725414117)
                ·
                  refine ⟨310936042300699073515147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1658325558937061725414117 310936042300699073515147)
                  ·
                    rfl

theorem cell22_2724956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 6, 4].length) (baseStart_2724956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724956 prefixEnd_2724956 := by exact prefixLift 2724956
  have htrace : WordTrace (prefixWord ++ tailWord_2724956) baseStart_2724956 baseEnd_2724956 := by
    simpa [prefixWord, tailWord_2724956, baseEnd_2724956] using wordTrace_append hprefix tailTrace_2724956
  have hstable : (prefixWord ++ tailWord_2724956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724956).length < 2 ^ (prefixWord ++ tailWord_2724956).sum := by decide
  have hdescent : baseEnd_2724956 < baseStart_2724956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724984 : List Nat := [2, 1, 2, 1, 1, 1, 8, 6]
def baseStart_2724984 : Nat := 118140960795 + 2724984 * 2 ^ 59
def prefixEnd_2724984 : Nat := 4983230072969 + 3 ^ 40 * 2724984 * 2
def baseEnd_2724984 : Nat := 103646412430479386760595

theorem tailTrace_2724984 : CollatzResearch.WordTrace tailWord_2724984 prefixEnd_2724984 103646412430479386760595 := by
  unfold tailWord_2724984
  simp only [CollatzResearch.WordTrace]
  refine ⟨49694165779927916530351003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66258887706570555373801337 49694165779927916530351003)
  ·
    refine ⟨74541248669891874795526505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49694165779927916530351003 74541248669891874795526505)
    ·
      refine ⟨55905936502418906096644879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74541248669891874795526505 55905936502418906096644879)
      ·
        refine ⟨83858904753628359144967319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55905936502418906096644879 83858904753628359144967319)
        ·
          refine ⟨125788357130442538717450979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83858904753628359144967319 125788357130442538717450979)
          ·
            refine ⟨188682535695663808076176469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125788357130442538717450979 188682535695663808076176469)
            ·
              refine ⟨2211123465183560250892693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 188682535695663808076176469 2211123465183560250892693)
              ·
                refine ⟨103646412430479386760595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2211123465183560250892693 103646412430479386760595)
                ·
                  rfl

theorem cell22_2724984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 6].length) (baseStart_2724984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2724984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2724984 prefixEnd_2724984 := by exact prefixLift 2724984
  have htrace : WordTrace (prefixWord ++ tailWord_2724984) baseStart_2724984 baseEnd_2724984 := by
    simpa [prefixWord, tailWord_2724984, baseEnd_2724984] using wordTrace_append hprefix tailTrace_2724984
  have hstable : (prefixWord ++ tailWord_2724984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724984).length < 2 ^ (prefixWord ++ tailWord_2724984).sum := by decide
  have hdescent : baseEnd_2724984 < baseStart_2724984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725022 : List Nat := [4, 3, 1, 1, 2, 3, 2, 1, 2, 3]
def baseStart_2725022 : Nat := 118140960795 + 2725022 * 2 ^ 59
def prefixEnd_2725022 : Nat := 4983230072969 + 3 ^ 40 * 2725022 * 2
def baseEnd_2725022 : Nat := 932830720050895048395239

theorem tailTrace_2725022 : CollatzResearch.WordTrace tailWord_2725022 prefixEnd_2725022 932830720050895048395239 := by
  unfold tailWord_2725022
  simp only [CollatzResearch.WordTrace]
  refine ⟨12423714691714770693823165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66259811689145443700390213 12423714691714770693823165)
  ·
    refine ⟨4658893009393039010183687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12423714691714770693823165 4658893009393039010183687)
    ·
      refine ⟨6988339514089558515275531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4658893009393039010183687 6988339514089558515275531)
      ·
        refine ⟨10482509271134337772913297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6988339514089558515275531 10482509271134337772913297)
        ·
          refine ⟨7861881953350753329684973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10482509271134337772913297 7861881953350753329684973)
          ·
            refine ⟨2948205732506532498631865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7861881953350753329684973 2948205732506532498631865)
            ·
              refine ⟨2211154299379899373973899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2948205732506532498631865 2211154299379899373973899)
              ·
                refine ⟨3316731449069849060960849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2211154299379899373973899 3316731449069849060960849)
                ·
                  refine ⟨2487548586802386795720637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3316731449069849060960849 2487548586802386795720637)
                  ·
                    refine ⟨932830720050895048395239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2487548586802386795720637 932830720050895048395239)
                    ·
                      rfl

theorem cell22_2725022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_2725022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2725022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2725022 prefixEnd_2725022 := by exact prefixLift 2725022
  have htrace : WordTrace (prefixWord ++ tailWord_2725022) baseStart_2725022 baseEnd_2725022 := by
    simpa [prefixWord, tailWord_2725022, baseEnd_2725022] using wordTrace_append hprefix tailTrace_2725022
  have hstable : (prefixWord ++ tailWord_2725022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725022).length < 2 ^ (prefixWord ++ tailWord_2725022).sum := by decide
  have hdescent : baseEnd_2725022 < baseStart_2725022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725119 : List Nat := [1, 1, 2, 2, 1, 6, 9]
def baseStart_2725119 : Nat := 118140960795 + 2725119 * 2 ^ 59
def prefixEnd_2725119 : Nat := 4983230072969 + 3 ^ 40 * 2725119 * 2
def baseEnd_2725119 : Nat := 34550515745674782545183

theorem tailTrace_2725119 : CollatzResearch.WordTrace tailWord_2725119 prefixEnd_2725119 34550515745674782545183 := by
  unfold tailWord_2725119
  simp only [CollatzResearch.WordTrace]
  refine ⟨99393255414366751116866411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66262170276244500744577607 99393255414366751116866411)
  ·
    refine ⟨149089883121550126675299617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99393255414366751116866411 149089883121550126675299617)
    ·
      refine ⟨111817412341162595006474713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149089883121550126675299617 111817412341162595006474713)
      ·
        refine ⟨83863059255871946254856035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111817412341162595006474713 83863059255871946254856035)
        ·
          refine ⟨125794588883807919382284053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83863059255871946254856035 125794588883807919382284053)
          ·
            refine ⟨5896621353928496221044565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 125794588883807919382284053 5896621353928496221044565)
            ·
              refine ⟨34550515745674782545183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5896621353928496221044565 34550515745674782545183)
              ·
                rfl

theorem cell22_2725119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 9].length) (baseStart_2725119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2725119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2725119 prefixEnd_2725119 := by exact prefixLift 2725119
  have htrace : WordTrace (prefixWord ++ tailWord_2725119) baseStart_2725119 baseEnd_2725119 := by
    simpa [prefixWord, tailWord_2725119, baseEnd_2725119] using wordTrace_append hprefix tailTrace_2725119
  have hstable : (prefixWord ++ tailWord_2725119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725119).length < 2 ^ (prefixWord ++ tailWord_2725119).sum := by decide
  have hdescent : baseEnd_2725119 < baseStart_2725119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725123 : List Nat := [1, 1, 1, 3, 2, 4, 3, 2, 2, 3]
def baseStart_2725123 : Nat := 118140960795 + 2725123 * 2 ^ 59
def prefixEnd_2725123 : Nat := 4983230072969 + 3 ^ 40 * 2725123 * 2
def baseEnd_2725123 : Nat := 932865294414964451619929

theorem tailTrace_2725123 : CollatzResearch.WordTrace tailWord_2725123 prefixEnd_2725123 932865294414964451619929 := by
  unfold tailWord_2725123
  simp only [CollatzResearch.WordTrace]
  refine ⟨99393401306352259800012023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66262267537568173200008015 99393401306352259800012023)
  ·
    refine ⟨149090101959528389700018035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99393401306352259800012023 149090101959528389700018035)
    ·
      refine ⟨223635152939292584550027053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149090101959528389700018035 223635152939292584550027053)
      ·
        refine ⟨83863182352234719206260145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223635152939292584550027053 83863182352234719206260145)
        ·
          refine ⟨62897386764176039404695109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83863182352234719206260145 62897386764176039404695109)
          ·
            refine ⟨11793260018283007388380333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62897386764176039404695109 11793260018283007388380333)
            ·
              refine ⟨4422472506856127770642625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11793260018283007388380333 4422472506856127770642625)
              ·
                refine ⟨3316854380142095827981969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4422472506856127770642625 3316854380142095827981969)
                ·
                  refine ⟨2487640785106571870986477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3316854380142095827981969 2487640785106571870986477)
                  ·
                    refine ⟨932865294414964451619929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2487640785106571870986477 932865294414964451619929)
                    ·
                      rfl

theorem cell22_2725123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 2, 3].length) (baseStart_2725123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2725123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2725123 prefixEnd_2725123 := by exact prefixLift 2725123
  have htrace : WordTrace (prefixWord ++ tailWord_2725123) baseStart_2725123 baseEnd_2725123 := by
    simpa [prefixWord, tailWord_2725123, baseEnd_2725123] using wordTrace_append hprefix tailTrace_2725123
  have hstable : (prefixWord ++ tailWord_2725123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725123).length < 2 ^ (prefixWord ++ tailWord_2725123).sum := by decide
  have hdescent : baseEnd_2725123 < baseStart_2725123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725185 : List Nat := [1, 2, 5, 2, 1, 1, 3, 1, 3, 3]
def baseStart_2725185 : Nat := 118140960795 + 2725185 * 2 ^ 59
def prefixEnd_2725185 : Nat := 4983230072969 + 3 ^ 40 * 2725185 * 2
def baseEnd_2725185 : Nat := 932886518282016956569739

theorem tailTrace_2725185 : CollatzResearch.WordTrace tailWord_2725185 prefixEnd_2725185 932886518282016956569739 := by
  unfold tailWord_2725185
  simp only [CollatzResearch.WordTrace]
  refine ⟨99395662632127644388769009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66263775088085096259179339 99395662632127644388769009)
  ·
    refine ⟨74546746974095733291576757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99395662632127644388769009 74546746974095733291576757)
    ·
      refine ⟨6988757528821474996085321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74546746974095733291576757 6988757528821474996085321)
      ·
        refine ⟨5241568146616106247063991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6988757528821474996085321 5241568146616106247063991)
        ·
          refine ⟨7862352219924159370595987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5241568146616106247063991 7862352219924159370595987)
          ·
            refine ⟨11793528329886239055893981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7862352219924159370595987 11793528329886239055893981)
            ·
              refine ⟨4422573123707339645960243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11793528329886239055893981 4422573123707339645960243)
              ·
                refine ⟨6633859685561009468940365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4422573123707339645960243 6633859685561009468940365)
                ·
                  refine ⟨2487697382085378550852637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6633859685561009468940365 2487697382085378550852637)
                  ·
                    refine ⟨932886518282016956569739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2487697382085378550852637 932886518282016956569739)
                    ·
                      rfl

theorem cell22_2725185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_2725185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2725185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2725185 prefixEnd_2725185 := by exact prefixLift 2725185
  have htrace : WordTrace (prefixWord ++ tailWord_2725185) baseStart_2725185 baseEnd_2725185 := by
    simpa [prefixWord, tailWord_2725185, baseEnd_2725185] using wordTrace_append hprefix tailTrace_2725185
  have hstable : (prefixWord ++ tailWord_2725185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725185).length < 2 ^ (prefixWord ++ tailWord_2725185).sum := by decide
  have hdescent : baseEnd_2725185 < baseStart_2725185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725243 : List Nat := [1, 1, 1, 1, 1, 6, 3, 4, 4]
def baseStart_2725243 : Nat := 118140960795 + 2725243 * 2 ^ 59
def prefixEnd_2725243 : Nat := 4983230072969 + 3 ^ 40 * 2725243 * 2
def baseEnd_2725243 : Nat := 310968790955774712873187

theorem tailTrace_2725243 : CollatzResearch.WordTrace tailWord_2725243 prefixEnd_2725243 310968790955774712873187 := by
  unfold tailWord_2725243
  simp only [CollatzResearch.WordTrace]
  refine ⟨99397778065917520294380383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66265185377278346862920255 99397778065917520294380383)
  ·
    refine ⟨149096667098876280441570575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99397778065917520294380383 149096667098876280441570575)
    ·
      refine ⟨223645000648314420662355863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149096667098876280441570575 223645000648314420662355863)
      ·
        refine ⟨335467500972471630993533795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223645000648314420662355863 335467500972471630993533795)
        ·
          refine ⟨503201251458707446490300693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335467500972471630993533795 503201251458707446490300693)
          ·
            refine ⟨23587558662126911554232845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 503201251458707446490300693 23587558662126911554232845)
            ·
              refine ⟨8845334498297591832837317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23587558662126911554232845 8845334498297591832837317)
              ·
                refine ⟨1658500218430798468656997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8845334498297591832837317 1658500218430798468656997)
                ·
                  refine ⟨310968790955774712873187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1658500218430798468656997 310968790955774712873187)
                  ·
                    rfl

theorem cell22_2725243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 4, 4].length) (baseStart_2725243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2725243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2725243 prefixEnd_2725243 := by exact prefixLift 2725243
  have htrace : WordTrace (prefixWord ++ tailWord_2725243) baseStart_2725243 baseEnd_2725243 := by
    simpa [prefixWord, tailWord_2725243, baseEnd_2725243] using wordTrace_append hprefix tailTrace_2725243
  have hstable : (prefixWord ++ tailWord_2725243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725243).length < 2 ^ (prefixWord ++ tailWord_2725243).sum := by decide
  have hdescent : baseEnd_2725243 < baseStart_2725243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725273 : List Nat := [1, 2, 1, 2, 1, 5, 3, 1, 2, 4]
def baseStart_2725273 : Nat := 118140960795 + 2725273 * 2 ^ 59
def prefixEnd_2725273 : Nat := 4983230072969 + 3 ^ 40 * 2725273 * 2
def baseEnd_2725273 : Nat := 932916642480414060369469

theorem tailTrace_2725273 : CollatzResearch.WordTrace tailWord_2725273 prefixEnd_2725273 932916642480414060369469 := by
  unfold tailWord_2725273
  simp only [CollatzResearch.WordTrace]
  refine ⟨99398872255808835417972473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66265914837205890278648315 99398872255808835417972473)
  ·
    refine ⟨74549154191856626563479355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99398872255808835417972473 74549154191856626563479355)
    ·
      refine ⟨111823731287784939845219033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74549154191856626563479355 111823731287784939845219033)
      ·
        refine ⟨83867798465838704883914275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111823731287784939845219033 83867798465838704883914275)
        ·
          refine ⟨125801697698758057325871413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83867798465838704883914275 125801697698758057325871413)
          ·
            refine ⟨11793909159258567874300445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125801697698758057325871413 11793909159258567874300445)
            ·
              refine ⟨4422715934721962952862667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11793909159258567874300445 4422715934721962952862667)
              ·
                refine ⟨6634073902082944429294001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4422715934721962952862667 6634073902082944429294001)
                ·
                  refine ⟨4975555426562208321970501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6634073902082944429294001 4975555426562208321970501)
                  ·
                    refine ⟨932916642480414060369469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4975555426562208321970501 932916642480414060369469)
                    ·
                      rfl

theorem cell22_2725273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 4].length) (baseStart_2725273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2725273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2725273 prefixEnd_2725273 := by exact prefixLift 2725273
  have htrace : WordTrace (prefixWord ++ tailWord_2725273) baseStart_2725273 baseEnd_2725273 := by
    simpa [prefixWord, tailWord_2725273, baseEnd_2725273] using wordTrace_append hprefix tailTrace_2725273
  have hstable : (prefixWord ++ tailWord_2725273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725273).length < 2 ^ (prefixWord ++ tailWord_2725273).sum := by decide
  have hdescent : baseEnd_2725273 < baseStart_2725273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725337 : List Nat := [1, 2, 1, 2, 4, 2, 3, 3, 1, 3]
def baseStart_2725337 : Nat := 118140960795 + 2725337 * 2 ^ 59
def prefixEnd_2725337 : Nat := 4983230072969 + 3 ^ 40 * 2725337 * 2
def baseEnd_2725337 : Nat := 932938550988339226769273

theorem tailTrace_2725337 : CollatzResearch.WordTrace tailWord_2725337 prefixEnd_2725337 932938550988339226769273 := by
  unfold tailWord_2725337
  simp only [CollatzResearch.WordTrace]
  refine ⟨99401206527576974348302265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66267471018384649565534843 99401206527576974348302265)
  ·
    refine ⟨74550904895682730761226699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99401206527576974348302265 74550904895682730761226699)
    ·
      refine ⟨111826357343524096141840049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74550904895682730761226699 111826357343524096141840049)
      ·
        refine ⟨83869768007643072106380037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111826357343524096141840049 83869768007643072106380037)
        ·
          refine ⟨15725581501433076019946257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83869768007643072106380037 15725581501433076019946257)
          ·
            refine ⟨11794186126074807014959693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15725581501433076019946257 11794186126074807014959693)
            ·
              refine ⟨4422819797278052630609885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11794186126074807014959693 4422819797278052630609885)
              ·
                refine ⟨1658557423979269736478707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4422819797278052630609885 1658557423979269736478707)
                ·
                  refine ⟨2487836135968904604718061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1658557423979269736478707 2487836135968904604718061)
                  ·
                    refine ⟨932938550988339226769273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2487836135968904604718061 932938550988339226769273)
                    ·
                      rfl

theorem cell22_2725337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 3, 1, 3].length) (baseStart_2725337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2725337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2725337 prefixEnd_2725337 := by exact prefixLift 2725337
  have htrace : WordTrace (prefixWord ++ tailWord_2725337) baseStart_2725337 baseEnd_2725337 := by
    simpa [prefixWord, tailWord_2725337, baseEnd_2725337] using wordTrace_append hprefix tailTrace_2725337
  have hstable : (prefixWord ++ tailWord_2725337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725337).length < 2 ^ (prefixWord ++ tailWord_2725337).sum := by decide
  have hdescent : baseEnd_2725337 < baseStart_2725337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725354 : List Nat := [3, 1, 3, 1, 5, 1, 1, 1, 3, 3]
def baseStart_2725354 : Nat := 118140960795 + 2725354 * 2 ^ 59
def prefixEnd_2725354 : Nat := 4983230072969 + 3 ^ 40 * 2725354 * 2
def baseEnd_2725354 : Nat := 932944370435756849094221

theorem tailTrace_2725354 : CollatzResearch.WordTrace tailWord_2725354 prefixEnd_2725354 932944370435756849094221 := by
  unfold tailWord_2725354
  simp only [CollatzResearch.WordTrace]
  refine ⟨24850456642128846562917779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66267884379010257501114077 24850456642128846562917779)
  ·
    refine ⟨37275684963193269844376669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24850456642128846562917779 37275684963193269844376669)
    ·
      refine ⟨13978381861197476191641251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37275684963193269844376669 13978381861197476191641251)
      ·
        refine ⟨20967572791796214287461877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13978381861197476191641251 20967572791796214287461877)
        ·
          refine ⟨1965709949230895089449551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20967572791796214287461877 1965709949230895089449551)
          ·
            refine ⟨2948564923846342634174327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1965709949230895089449551 2948564923846342634174327)
            ·
              refine ⟨4422847385769513951261491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2948564923846342634174327 4422847385769513951261491)
              ·
                refine ⟨6634271078654270926892237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4422847385769513951261491 6634271078654270926892237)
                ·
                  refine ⟨2487851654495351597584589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6634271078654270926892237 2487851654495351597584589)
                  ·
                    refine ⟨932944370435756849094221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2487851654495351597584589 932944370435756849094221)
                    ·
                      rfl

theorem cell22_2725354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_2725354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2725354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2725354 prefixEnd_2725354 := by exact prefixLift 2725354
  have htrace : WordTrace (prefixWord ++ tailWord_2725354) baseStart_2725354 baseEnd_2725354 := by
    simpa [prefixWord, tailWord_2725354, baseEnd_2725354] using wordTrace_append hprefix tailTrace_2725354
  have hstable : (prefixWord ++ tailWord_2725354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725354).length < 2 ^ (prefixWord ++ tailWord_2725354).sum := by decide
  have hdescent : baseEnd_2725354 < baseStart_2725354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725393 : List Nat := [1, 2, 2, 1, 1, 2, 5, 2, 1, 5]
def baseStart_2725393 : Nat := 118140960795 + 2725393 * 2 ^ 59
def prefixEnd_2725393 : Nat := 4983230072969 + 3 ^ 40 * 2725393 * 2
def baseEnd_2725393 : Nat := 932957720932773747369101

theorem tailTrace_2725393 : CollatzResearch.WordTrace tailWord_2725393 prefixEnd_2725393 932957720932773747369101 := by
  unfold tailWord_2725393
  simp only [CollatzResearch.WordTrace]
  refine ⟨99403249015374095912340833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66268832676916063941560555 99403249015374095912340833)
  ·
    refine ⟨74552436761530571934255625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99403249015374095912340833 74552436761530571934255625)
    ·
      refine ⟨55914327571147928950691719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74552436761530571934255625 55914327571147928950691719)
      ·
        refine ⟨83871491356721893426037579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55914327571147928950691719 83871491356721893426037579)
        ·
          refine ⟨125807237035082840139056369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83871491356721893426037579 125807237035082840139056369)
          ·
            refine ⟨94355427776312130104292277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125807237035082840139056369 94355427776312130104292277)
            ·
              refine ⟨8845821354029262197277401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94355427776312130104292277 8845821354029262197277401)
              ·
                refine ⟨6634366015521946647958051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8845821354029262197277401 6634366015521946647958051)
                ·
                  refine ⟨9951549023282919971937077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6634366015521946647958051 9951549023282919971937077)
                  ·
                    refine ⟨932957720932773747369101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9951549023282919971937077 932957720932773747369101)
                    ·
                      rfl

theorem cell22_2725393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_2725393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2725393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2725393 prefixEnd_2725393 := by exact prefixLift 2725393
  have htrace : WordTrace (prefixWord ++ tailWord_2725393) baseStart_2725393 baseEnd_2725393 := by
    simpa [prefixWord, tailWord_2725393, baseEnd_2725393] using wordTrace_append hprefix tailTrace_2725393
  have hstable : (prefixWord ++ tailWord_2725393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725393).length < 2 ^ (prefixWord ++ tailWord_2725393).sum := by decide
  have hdescent : baseEnd_2725393 < baseStart_2725393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725397 : List Nat := [1, 3, 2, 1, 3, 3, 3, 1, 1, 4]
def baseStart_2725397 : Nat := 118140960795 + 2725397 * 2 ^ 59
def prefixEnd_2725397 : Nat := 4983230072969 + 3 ^ 40 * 2725397 * 2
def baseEnd_2725397 : Nat := 932959090214519070269089

theorem tailTrace_2725397 : CollatzResearch.WordTrace tailWord_2725397 prefixEnd_2725397 932959090214519070269089 := by
  unfold tailWord_2725397
  simp only [CollatzResearch.WordTrace]
  refine ⟨99403394907359604595486445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66268929938239736396990963 99403394907359604595486445)
  ·
    refine ⟨37276273090259851723307417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99403394907359604595486445 37276273090259851723307417)
    ·
      refine ⟨27957204817694888792480563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37276273090259851723307417 27957204817694888792480563)
      ·
        refine ⟨41935807226542333188720845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27957204817694888792480563 41935807226542333188720845)
        ·
          refine ⟨15725927709953374945770317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41935807226542333188720845 15725927709953374945770317)
          ·
            refine ⟨5897222891232515604663869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15725927709953374945770317 5897222891232515604663869)
            ·
              refine ⟨2211458584212193351748951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5897222891232515604663869 2211458584212193351748951)
              ·
                refine ⟨3317187876318290027623427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2211458584212193351748951 3317187876318290027623427)
                ·
                  refine ⟨4975781814477435041435141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3317187876318290027623427 4975781814477435041435141)
                  ·
                    refine ⟨932959090214519070269089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4975781814477435041435141 932959090214519070269089)
                    ·
                      rfl

theorem cell22_2725397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_2725397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2725397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2725397 prefixEnd_2725397 := by exact prefixLift 2725397
  have htrace : WordTrace (prefixWord ++ tailWord_2725397) baseStart_2725397 baseEnd_2725397 := by
    simpa [prefixWord, tailWord_2725397, baseEnd_2725397] using wordTrace_append hprefix tailTrace_2725397
  have hstable : (prefixWord ++ tailWord_2725397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725397).length < 2 ^ (prefixWord ++ tailWord_2725397).sum := by decide
  have hdescent : baseEnd_2725397 < baseStart_2725397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725410 : List Nat := [3, 3, 1, 1, 1, 1, 2, 3, 4, 3]
def baseStart_2725410 : Nat := 118140960795 + 2725410 * 2 ^ 59
def prefixEnd_2725410 : Nat := 4983230072969 + 3 ^ 40 * 2725410 * 2
def baseEnd_2725410 : Nat := 932963540380191369694049

theorem tailTrace_2725410 : CollatzResearch.WordTrace tailWord_2725410 prefixEnd_2725410 932963540380191369694049 := by
  unfold tailWord_2725410
  simp only [CollatzResearch.WordTrace]
  refine ⟨24850967264078126953927421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66269246037541671877139789 24850967264078126953927421)
  ·
    refine ⟨9319112724029297607722783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24850967264078126953927421 9319112724029297607722783)
    ·
      refine ⟨13978669086043946411584175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9319112724029297607722783 13978669086043946411584175)
      ·
        refine ⟨20968003629065919617376263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13978669086043946411584175 20968003629065919617376263)
        ·
          refine ⟨31452005443598879426064395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20968003629065919617376263 31452005443598879426064395)
          ·
            refine ⟨47178008165398319139096593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31452005443598879426064395 47178008165398319139096593)
            ·
              refine ⟨35383506124048739354322445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47178008165398319139096593 35383506124048739354322445)
              ·
                refine ⟨13268814796518277257870917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35383506124048739354322445 13268814796518277257870917)
                ·
                  refine ⟨2487902774347176985850797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13268814796518277257870917 2487902774347176985850797)
                  ·
                    refine ⟨932963540380191369694049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2487902774347176985850797 932963540380191369694049)
                    ·
                      rfl

theorem cell22_2725410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_2725410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2725410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2725410 prefixEnd_2725410 := by exact prefixLift 2725410
  have htrace : WordTrace (prefixWord ++ tailWord_2725410) baseStart_2725410 baseEnd_2725410 := by
    simpa [prefixWord, tailWord_2725410, baseEnd_2725410] using wordTrace_append hprefix tailTrace_2725410
  have hstable : (prefixWord ++ tailWord_2725410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725410).length < 2 ^ (prefixWord ++ tailWord_2725410).sum := by decide
  have hdescent : baseEnd_2725410 < baseStart_2725410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725446 : List Nat := [6, 1, 1, 1, 3, 1, 2, 3, 4]
def baseStart_2725446 : Nat := 118140960795 + 2725446 * 2 ^ 59
def prefixEnd_2725446 : Nat := 4983230072969 + 3 ^ 40 * 2725446 * 2
def baseEnd_2725446 : Nat := 310991954638633091931313

theorem tailTrace_2725446 : CollatzResearch.WordTrace tailWord_2725446 prefixEnd_2725446 310991954638633091931313 := by
  unfold tailWord_2725446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3106411940130690186375631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 66270121389454723976013461 3106411940130690186375631)
  ·
    refine ⟨4659617910196035279563447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3106411940130690186375631 4659617910196035279563447)
    ·
      refine ⟨6989426865294052919345171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4659617910196035279563447 6989426865294052919345171)
      ·
        refine ⟨10484140297941079379017757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6989426865294052919345171 10484140297941079379017757)
        ·
          refine ⟨3931552611727904767131659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10484140297941079379017757 3931552611727904767131659)
          ·
            refine ⟨5897328917591857150697489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3931552611727904767131659 5897328917591857150697489)
            ·
              refine ⟨4422996688193892863023117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5897328917591857150697489 4422996688193892863023117)
              ·
                refine ⟨1658623758072709823633669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4422996688193892863023117 1658623758072709823633669)
                ·
                  refine ⟨310991954638633091931313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1658623758072709823633669 310991954638633091931313)
                  ·
                    rfl

theorem cell22_2725446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_2725446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2725446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2725446 prefixEnd_2725446 := by exact prefixLift 2725446
  have htrace : WordTrace (prefixWord ++ tailWord_2725446) baseStart_2725446 baseEnd_2725446 := by
    simpa [prefixWord, tailWord_2725446, baseEnd_2725446] using wordTrace_append hprefix tailTrace_2725446
  have hstable : (prefixWord ++ tailWord_2725446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725446).length < 2 ^ (prefixWord ++ tailWord_2725446).sum := by decide
  have hdescent : baseEnd_2725446 < baseStart_2725446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725513 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 8]
def baseStart_2725513 : Nat := 118140960795 + 2725513 * 2 ^ 59
def prefixEnd_2725513 : Nat := 4983230072969 + 3 ^ 40 * 2725513 * 2
def baseEnd_2725513 : Nat := 310999599795044478122911

theorem tailTrace_2725513 : CollatzResearch.WordTrace tailWord_2725513 prefixEnd_2725513 310999599795044478122911 := by
  unfold tailWord_2725513
  simp only [CollatzResearch.WordTrace]
  refine ⟨99407625774939356406709193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66271750516626237604472795 99407625774939356406709193)
  ·
    refine ⟨74555719331204517305031895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99407625774939356406709193 74555719331204517305031895)
    ·
      refine ⟨111833578996806775957547843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74555719331204517305031895 111833578996806775957547843)
      ·
        refine ⟨167750368495210163936321765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111833578996806775957547843 167750368495210163936321765)
        ·
          refine ⟨31453194092851905738060331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167750368495210163936321765 31453194092851905738060331)
          ·
            refine ⟨47179791139277858607090497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31453194092851905738060331 47179791139277858607090497)
            ·
              refine ⟨35384843354458393955317873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47179791139277858607090497 35384843354458393955317873)
              ·
                refine ⟨26538632515843795466488405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35384843354458393955317873 26538632515843795466488405)
                ·
                  refine ⟨310999599795044478122911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26538632515843795466488405 310999599795044478122911)
                  ·
                    rfl

theorem cell22_2725513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 8].length) (baseStart_2725513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2725513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2725513 prefixEnd_2725513 := by exact prefixLift 2725513
  have htrace : WordTrace (prefixWord ++ tailWord_2725513) baseStart_2725513 baseEnd_2725513 := by
    simpa [prefixWord, tailWord_2725513, baseEnd_2725513] using wordTrace_append hprefix tailTrace_2725513
  have hstable : (prefixWord ++ tailWord_2725513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725513).length < 2 ^ (prefixWord ++ tailWord_2725513).sum := by decide
  have hdescent : baseEnd_2725513 < baseStart_2725513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725515 : List Nat := [1, 1, 1, 1, 4, 1, 3, 5, 1, 4]
def baseStart_2725515 : Nat := 118140960795 + 2725515 * 2 ^ 59
def prefixEnd_2725515 : Nat := 4983230072969 + 3 ^ 40 * 2725515 * 2
def baseEnd_2725515 : Nat := 932999484026006095818727

theorem tailTrace_2725515 : CollatzResearch.WordTrace tailWord_2725515 prefixEnd_2725515 932999484026006095818727 := by
  unfold tailWord_2725515
  simp only [CollatzResearch.WordTrace]
  refine ⟨99407698720932110748281999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66271799147288073832187999 99407698720932110748281999)
  ·
    refine ⟨149111548081398166122422999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99407698720932110748281999 149111548081398166122422999)
    ·
      refine ⟨223667322122097249183634499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149111548081398166122422999 223667322122097249183634499)
      ·
        refine ⟨335500983183145873775451749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223667322122097249183634499 335500983183145873775451749)
        ·
          refine ⟨62906434346839851332897203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 335500983183145873775451749 62906434346839851332897203)
          ·
            refine ⟨94359651520259776999345805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62906434346839851332897203 94359651520259776999345805)
            ·
              refine ⟨35384869320097416374754677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94359651520259776999345805 35384869320097416374754677)
              ·
                refine ⟨3317331498759132785133251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35384869320097416374754677 3317331498759132785133251)
                ·
                  refine ⟨4975997248138699177699877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3317331498759132785133251 4975997248138699177699877)
                  ·
                    refine ⟨932999484026006095818727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4975997248138699177699877 932999484026006095818727)
                    ·
                      rfl

theorem cell22_2725515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 4].length) (baseStart_2725515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2725515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2725515 prefixEnd_2725515 := by exact prefixLift 2725515
  have htrace : WordTrace (prefixWord ++ tailWord_2725515) baseStart_2725515 baseEnd_2725515 := by
    simpa [prefixWord, tailWord_2725515, baseEnd_2725515] using wordTrace_append hprefix tailTrace_2725515
  have hstable : (prefixWord ++ tailWord_2725515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725515).length < 2 ^ (prefixWord ++ tailWord_2725515).sum := by decide
  have hdescent : baseEnd_2725515 < baseStart_2725515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725581 : List Nat := [1, 6, 2, 1, 1, 2, 1, 4, 4]
def baseStart_2725581 : Nat := 118140960795 + 2725581 * 2 ^ 59
def prefixEnd_2725581 : Nat := 4983230072969 + 3 ^ 40 * 2725581 * 2
def baseEnd_2725581 : Nat := 311007359058267974556175

theorem tailTrace_2725581 : CollatzResearch.WordTrace tailWord_2725581 prefixEnd_2725581 311007359058267974556175 := by
  unfold tailWord_2725581
  simp only [CollatzResearch.WordTrace]
  refine ⟨99410105938693004020184597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66273403959128669346789731 99410105938693004020184597)
  ·
    refine ⟨4659848715876234563446153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 99410105938693004020184597 4659848715876234563446153)
    ·
      refine ⟨3494886536907175922584615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4659848715876234563446153 3494886536907175922584615)
      ·
        refine ⟨5242329805360763883876923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3494886536907175922584615 5242329805360763883876923)
        ·
          refine ⟨7863494708041145825815385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5242329805360763883876923 7863494708041145825815385)
          ·
            refine ⟨5897621031030859369361539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7863494708041145825815385 5897621031030859369361539)
            ·
              refine ⟨8846431546546289054042309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5897621031030859369361539 8846431546546289054042309)
              ·
                refine ⟨1658705914977429197632933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8846431546546289054042309 1658705914977429197632933)
                ·
                  refine ⟨311007359058267974556175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1658705914977429197632933 311007359058267974556175)
                  ·
                    rfl

theorem cell22_2725581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_2725581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2725581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2725581 prefixEnd_2725581 := by exact prefixLift 2725581
  have htrace : WordTrace (prefixWord ++ tailWord_2725581) baseStart_2725581 baseEnd_2725581 := by
    simpa [prefixWord, tailWord_2725581, baseEnd_2725581] using wordTrace_append hprefix tailTrace_2725581
  have hstable : (prefixWord ++ tailWord_2725581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725581).length < 2 ^ (prefixWord ++ tailWord_2725581).sum := by decide
  have hdescent : baseEnd_2725581 < baseStart_2725581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725605 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 2, 6]
def baseStart_2725605 : Nat := 118140960795 + 2725605 * 2 ^ 59
def prefixEnd_2725605 : Nat := 4983230072969 + 3 ^ 40 * 2725605 * 2
def baseEnd_2725605 : Nat := 933030292865275861068451

theorem tailTrace_2725605 : CollatzResearch.WordTrace tailWord_2725605 prefixEnd_2725605 933030292865275861068451 := by
  unfold tailWord_2725605
  simp only [CollatzResearch.WordTrace]
  refine ⟨99410981290606056119058269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66273987527070704079372179 99410981290606056119058269)
  ·
    refine ⟨37279117983977271044646851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99410981290606056119058269 37279117983977271044646851)
    ·
      refine ⟨55918676975965906566970277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37279117983977271044646851 55918676975965906566970277)
      ·
        refine ⟨10484751932993607481306927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55918676975965906566970277 10484751932993607481306927)
        ·
          refine ⟨15727127899490411221960391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10484751932993607481306927 15727127899490411221960391)
          ·
            refine ⟨23590691849235616832940587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15727127899490411221960391 23590691849235616832940587)
            ·
              refine ⟨35386037773853425249410881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23590691849235616832940587 35386037773853425249410881)
              ·
                refine ⟨26539528330390068937058161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35386037773853425249410881 26539528330390068937058161)
                ·
                  refine ⟨19904646247792551702793621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26539528330390068937058161 19904646247792551702793621)
                  ·
                    refine ⟨933030292865275861068451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19904646247792551702793621 933030292865275861068451)
                    ·
                      rfl

theorem cell22_2725605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_2725605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2725605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2725605 prefixEnd_2725605 := by exact prefixLift 2725605
  have htrace : WordTrace (prefixWord ++ tailWord_2725605) baseStart_2725605 baseEnd_2725605 := by
    simpa [prefixWord, tailWord_2725605, baseEnd_2725605] using wordTrace_append hprefix tailTrace_2725605
  have hstable : (prefixWord ++ tailWord_2725605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725605).length < 2 ^ (prefixWord ++ tailWord_2725605).sum := by decide
  have hdescent : baseEnd_2725605 < baseStart_2725605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725635 : List Nat := [1, 1, 1, 3, 2, 2, 3, 2, 2, 5]
def baseStart_2725635 : Nat := 118140960795 + 2725635 * 2 ^ 59
def prefixEnd_2725635 : Nat := 4983230072969 + 3 ^ 40 * 2725635 * 2
def baseEnd_2725635 : Nat := 933040562478365782818359

theorem tailTrace_2725635 : CollatzResearch.WordTrace tailWord_2725635 prefixEnd_2725635 933040562478365782818359 := by
  unfold tailWord_2725635
  simp only [CollatzResearch.WordTrace]
  refine ⟨99412075480497371242650359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66274716986998247495100239 99412075480497371242650359)
  ·
    refine ⟨149118113220746056863975539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99412075480497371242650359 149118113220746056863975539)
    ·
      refine ⟨223677169831119085295963309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149118113220746056863975539 223677169831119085295963309)
      ·
        refine ⟨83878938686669656985986241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223677169831119085295963309 83878938686669656985986241)
        ·
          refine ⟨62909204015002242739489681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83878938686669656985986241 62909204015002242739489681)
          ·
            refine ⟨47181903011251682054617261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62909204015002242739489681 47181903011251682054617261)
            ·
              refine ⟨17693213629219380770481473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47181903011251682054617261 17693213629219380770481473)
              ·
                refine ⟨13269910221914535577861105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17693213629219380770481473 13269910221914535577861105)
                ·
                  refine ⟨9952432666435901683395829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13269910221914535577861105 9952432666435901683395829)
                  ·
                    refine ⟨933040562478365782818359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9952432666435901683395829 933040562478365782818359)
                    ·
                      rfl

theorem cell22_2725635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 5].length) (baseStart_2725635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2725635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2725635 prefixEnd_2725635 := by exact prefixLift 2725635
  have htrace : WordTrace (prefixWord ++ tailWord_2725635) baseStart_2725635 baseEnd_2725635 := by
    simpa [prefixWord, tailWord_2725635, baseEnd_2725635] using wordTrace_append hprefix tailTrace_2725635
  have hstable : (prefixWord ++ tailWord_2725635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725635).length < 2 ^ (prefixWord ++ tailWord_2725635).sum := by decide
  have hdescent : baseEnd_2725635 < baseStart_2725635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725667 : List Nat := [1, 1, 1, 4, 2, 1, 3, 4, 1, 4]
def baseStart_2725667 : Nat := 118140960795 + 2725667 * 2 ^ 59
def prefixEnd_2725667 : Nat := 4983230072969 + 3 ^ 40 * 2725667 * 2
def baseEnd_2725667 : Nat := 933051516732328366018261

theorem tailTrace_2725667 : CollatzResearch.WordTrace tailWord_2725667 prefixEnd_2725667 933051516732328366018261 := by
  unfold tailWord_2725667
  simp only [CollatzResearch.WordTrace]
  refine ⟨99413242616381440707815255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66275495077587627138543503 99413242616381440707815255)
  ·
    refine ⟨149119863924572161061722883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99413242616381440707815255 149119863924572161061722883)
    ·
      refine ⟨223679795886858241592584325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149119863924572161061722883 223679795886858241592584325)
      ·
        refine ⟨41939961728785920298609561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 223679795886858241592584325 41939961728785920298609561)
        ·
          refine ⟨31454971296589440223957171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41939961728785920298609561 31454971296589440223957171)
          ·
            refine ⟨47182456944884160335935757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31454971296589440223957171 47182456944884160335935757)
            ·
              refine ⟨17693421354331560125975909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47182456944884160335935757 17693421354331560125975909)
              ·
                refine ⟨3317516503937167523620483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17693421354331560125975909 3317516503937167523620483)
                ·
                  refine ⟨4976274755905751285430725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3317516503937167523620483 4976274755905751285430725)
                  ·
                    refine ⟨933051516732328366018261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4976274755905751285430725 933051516732328366018261)
                    ·
                      rfl

theorem cell22_2725667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 4].length) (baseStart_2725667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2725667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2725667 prefixEnd_2725667 := by exact prefixLift 2725667
  have htrace : WordTrace (prefixWord ++ tailWord_2725667) baseStart_2725667 baseEnd_2725667 := by
    simpa [prefixWord, tailWord_2725667, baseEnd_2725667] using wordTrace_append hprefix tailTrace_2725667
  have hstable : (prefixWord ++ tailWord_2725667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725667).length < 2 ^ (prefixWord ++ tailWord_2725667).sum := by decide
  have hdescent : baseEnd_2725667 < baseStart_2725667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725750 : List Nat := [5, 1, 1, 3, 2, 2, 2, 2, 4]
def baseStart_2725750 : Nat := 118140960795 + 2725750 * 2 ^ 59
def prefixEnd_2725750 : Nat := 4983230072969 + 3 ^ 40 * 2725750 * 2
def baseEnd_2725750 : Nat := 311026643109514605397669

theorem tailTrace_2725750 : CollatzResearch.WordTrace tailWord_2725750 prefixEnd_2725750 311026643109514605397669 := by
  unfold tailWord_2725750
  simp only [CollatzResearch.WordTrace]
  refine ⟨6213516867192546617692919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66277513250053830588724469 6213516867192546617692919)
  ·
    refine ⟨9320275300788819926539379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6213516867192546617692919 9320275300788819926539379)
    ·
      refine ⟨13980412951183229889809069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9320275300788819926539379 13980412951183229889809069)
      ·
        refine ⟨5242654856693711208678401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13980412951183229889809069 5242654856693711208678401)
        ·
          refine ⟨3931991142520283406508801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5242654856693711208678401 3931991142520283406508801)
          ·
            refine ⟨2948993356890212554881601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3931991142520283406508801 2948993356890212554881601)
            ·
              refine ⟨2211745017667659416161201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2948993356890212554881601 2211745017667659416161201)
              ·
                refine ⟨1658808763250744562120901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2211745017667659416161201 1658808763250744562120901)
                ·
                  refine ⟨311026643109514605397669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1658808763250744562120901 311026643109514605397669)
                  ·
                    rfl

theorem cell22_2725750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_2725750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2725750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2725750 prefixEnd_2725750 := by exact prefixLift 2725750
  have htrace : WordTrace (prefixWord ++ tailWord_2725750) baseStart_2725750 baseEnd_2725750 := by
    simpa [prefixWord, tailWord_2725750, baseEnd_2725750] using wordTrace_append hprefix tailTrace_2725750
  have hstable : (prefixWord ++ tailWord_2725750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725750).length < 2 ^ (prefixWord ++ tailWord_2725750).sum := by decide
  have hdescent : baseEnd_2725750 < baseStart_2725750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725761 : List Nat := [1, 2, 4, 4, 1, 2, 1, 7]
def baseStart_2725761 : Nat := 118140960795 + 2725761 * 2 ^ 59
def prefixEnd_2725761 : Nat := 4983230072969 + 3 ^ 40 * 2725761 * 2
def baseEnd_2725761 : Nat := 103675966094815939351997

theorem tailTrace_2725761 : CollatzResearch.WordTrace tailWord_2725761 prefixEnd_2725761 103675966094815939351997 := by
  unfold tailWord_2725761
  simp only [CollatzResearch.WordTrace]
  refine ⟨99416671078040894761737137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66277780718693929841158091 99416671078040894761737137)
  ·
    refine ⟨74562503308530671071302853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99416671078040894761737137 74562503308530671071302853)
    ·
      refine ⟨13980469370349500825869285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74562503308530671071302853 13980469370349500825869285)
      ·
        refine ⟨2621338006940531404850491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13980469370349500825869285 2621338006940531404850491)
        ·
          refine ⟨3932007010410797107275737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2621338006940531404850491 3932007010410797107275737)
          ·
            refine ⟨2949005257808097830456803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3932007010410797107275737 2949005257808097830456803)
            ·
              refine ⟨4423507886712146745685205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2949005257808097830456803 4423507886712146745685205)
              ·
                refine ⟨103675966094815939351997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4423507886712146745685205 103675966094815939351997)
                ·
                  rfl

theorem cell22_2725761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 7].length) (baseStart_2725761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2725761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2725761 prefixEnd_2725761 := by exact prefixLift 2725761
  have htrace : WordTrace (prefixWord ++ tailWord_2725761) baseStart_2725761 baseEnd_2725761 := by
    simpa [prefixWord, tailWord_2725761, baseEnd_2725761] using wordTrace_append hprefix tailTrace_2725761
  have hstable : (prefixWord ++ tailWord_2725761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725761).length < 2 ^ (prefixWord ++ tailWord_2725761).sum := by decide
  have hdescent : baseEnd_2725761 < baseStart_2725761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725836 : List Nat := [2, 2, 1, 4, 1, 3, 2, 2, 1, 4]
def baseStart_2725836 : Nat := 118140960795 + 2725836 * 2 ^ 59
def prefixEnd_2725836 : Nat := 4983230072969 + 3 ^ 40 * 2725836 * 2
def baseEnd_2725836 : Nat := 933109368886068258542743

theorem tailTrace_2725836 : CollatzResearch.WordTrace tailWord_2725836 prefixEnd_2725836 933109368886068258542743 := by
  unfold tailWord_2725836
  simp only [CollatzResearch.WordTrace]
  refine ⟨49709703276384591285358681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66279604368512788380478241 49709703276384591285358681)
  ·
    refine ⟨37282277457288443464019011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49709703276384591285358681 37282277457288443464019011)
    ·
      refine ⟨55923416185932665196028517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37282277457288443464019011 55923416185932665196028517)
      ·
        refine ⟨10485640534862374724255347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55923416185932665196028517 10485640534862374724255347)
        ·
          refine ⟨15728460802293562086383021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10485640534862374724255347 15728460802293562086383021)
          ·
            refine ⟨5898172800860085782393633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15728460802293562086383021 5898172800860085782393633)
            ·
              refine ⟨4423629600645064336795225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5898172800860085782393633 4423629600645064336795225)
              ·
                refine ⟨3317722200483798252596419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4423629600645064336795225 3317722200483798252596419)
                ·
                  refine ⟨4976583300725697378894629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3317722200483798252596419 4976583300725697378894629)
                  ·
                    refine ⟨933109368886068258542743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4976583300725697378894629 933109368886068258542743)
                    ·
                      rfl

theorem cell22_2725836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_2725836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2725836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2725836 prefixEnd_2725836 := by exact prefixLift 2725836
  have htrace : WordTrace (prefixWord ++ tailWord_2725836) baseStart_2725836 baseEnd_2725836 := by
    simpa [prefixWord, tailWord_2725836, baseEnd_2725836] using wordTrace_append hprefix tailTrace_2725836
  have hstable : (prefixWord ++ tailWord_2725836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725836).length < 2 ^ (prefixWord ++ tailWord_2725836).sum := by decide
  have hdescent : baseEnd_2725836 < baseStart_2725836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725847 : List Nat := [1, 1, 3, 2, 1, 1, 3, 3, 1, 6]
def baseStart_2725847 : Nat := 118140960795 + 2725847 * 2 ^ 59
def prefixEnd_2725847 : Nat := 4983230072969 + 3 ^ 40 * 2725847 * 2
def baseEnd_2725847 : Nat := 933113134410867896517709

theorem tailTrace_2725847 : CollatzResearch.WordTrace tailWord_2725847 prefixEnd_2725847 933113134410867896517709 := by
  unfold tailWord_2725847
  simp only [CollatzResearch.WordTrace]
  refine ⟨99419807755729331449367795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66279871837152887632911863 99419807755729331449367795)
  ·
    refine ⟨149129711633593997174051693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99419807755729331449367795 149129711633593997174051693)
    ·
      refine ⟨55923641862597748940269385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149129711633593997174051693 55923641862597748940269385)
      ·
        refine ⟨41942731396948311705202039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55923641862597748940269385 41942731396948311705202039)
        ·
          refine ⟨62914097095422467557803059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41942731396948311705202039 62914097095422467557803059)
          ·
            refine ⟨94371145643133701336704589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62914097095422467557803059 94371145643133701336704589)
            ·
              refine ⟨35389179616175138001264221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94371145643133701336704589 35389179616175138001264221)
              ·
                refine ⟨13270942356065676750474083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35389179616175138001264221 13270942356065676750474083)
                ·
                  refine ⟨19906413534098515125711125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13270942356065676750474083 19906413534098515125711125)
                  ·
                    refine ⟨933113134410867896517709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19906413534098515125711125 933113134410867896517709)
                    ·
                      rfl

theorem cell22_2725847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_2725847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2725847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2725847 prefixEnd_2725847 := by exact prefixLift 2725847
  have htrace : WordTrace (prefixWord ++ tailWord_2725847) baseStart_2725847 baseEnd_2725847 := by
    simpa [prefixWord, tailWord_2725847, baseEnd_2725847] using wordTrace_append hprefix tailTrace_2725847
  have hstable : (prefixWord ++ tailWord_2725847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725847).length < 2 ^ (prefixWord ++ tailWord_2725847).sum := by decide
  have hdescent : baseEnd_2725847 < baseStart_2725847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725866 : List Nat := [3, 1, 3, 1, 2, 1, 2, 4, 2, 3]
def baseStart_2725866 : Nat := 118140960795 + 2725866 * 2 ^ 59
def prefixEnd_2725866 : Nat := 4983230072969 + 3 ^ 40 * 2725866 * 2
def baseEnd_2725866 : Nat := 933119638499158180292651

theorem tailTrace_2725866 : CollatzResearch.WordTrace tailWord_2725866 prefixEnd_2725866 933119638499158180292651 := by
  unfold tailWord_2725866
  simp only [CollatzResearch.WordTrace]
  refine ⟨24855125185665124423577363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66280333828440331796206301 24855125185665124423577363)
  ·
    refine ⟨37282687778497686635366045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24855125185665124423577363 37282687778497686635366045)
    ·
      refine ⟨13981007916936632488262267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37282687778497686635366045 13981007916936632488262267)
      ·
        refine ⟨20971511875404948732393401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13981007916936632488262267 20971511875404948732393401)
        ·
          refine ⟨15728633906553711549295051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20971511875404948732393401 15728633906553711549295051)
          ·
            refine ⟨23592950859830567323942577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15728633906553711549295051 23592950859830567323942577)
            ·
              refine ⟨17694713144872925492956933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23592950859830567323942577 17694713144872925492956933)
              ·
                refine ⟨3317758714663673529929425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17694713144872925492956933 3317758714663673529929425)
                ·
                  refine ⟨2488319035997755147447069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3317758714663673529929425 2488319035997755147447069)
                  ·
                    refine ⟨933119638499158180292651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2488319035997755147447069 933119638499158180292651)
                    ·
                      rfl

theorem cell22_2725866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_2725866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2725866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2725866 prefixEnd_2725866 := by exact prefixLift 2725866
  have htrace : WordTrace (prefixWord ++ tailWord_2725866) baseStart_2725866 baseEnd_2725866 := by
    simpa [prefixWord, tailWord_2725866, baseEnd_2725866] using wordTrace_append hprefix tailTrace_2725866
  have hstable : (prefixWord ++ tailWord_2725866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725866).length < 2 ^ (prefixWord ++ tailWord_2725866).sum := by decide
  have hdescent : baseEnd_2725866 < baseStart_2725866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725907 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 9]
def baseStart_2725907 : Nat := 118140960795 + 2725907 * 2 ^ 59
def prefixEnd_2725907 : Nat := 4983230072969 + 3 ^ 40 * 2725907 * 2
def baseEnd_2725907 : Nat := 311044557879015913339175

theorem tailTrace_2725907 : CollatzResearch.WordTrace tailWord_2725907 prefixEnd_2725907 311044557879015913339175 := by
  unfold tailWord_2725907
  simp only [CollatzResearch.WordTrace]
  refine ⟨99421996135511961696551975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66281330757007974464367983 99421996135511961696551975)
  ·
    refine ⟨149132994203267942544827963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99421996135511961696551975 149132994203267942544827963)
    ·
      refine ⟨223699491304901913817241945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149132994203267942544827963 223699491304901913817241945)
      ·
        refine ⟨167774618478676435362931459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223699491304901913817241945 167774618478676435362931459)
        ·
          refine ⟨251661927718014653044397189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167774618478676435362931459 251661927718014653044397189)
          ·
            refine ⟨47186611447127747445824473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 251661927718014653044397189 47186611447127747445824473)
            ·
              refine ⟨35389958585345810584368355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47186611447127747445824473 35389958585345810584368355)
              ·
                refine ⟨53084937878018715876552533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35389958585345810584368355 53084937878018715876552533)
                ·
                  refine ⟨311044557879015913339175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53084937878018715876552533 311044557879015913339175)
                  ·
                    rfl

theorem cell22_2725907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 9].length) (baseStart_2725907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2725907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2725907 prefixEnd_2725907 := by exact prefixLift 2725907
  have htrace : WordTrace (prefixWord ++ tailWord_2725907) baseStart_2725907 baseEnd_2725907 := by
    simpa [prefixWord, tailWord_2725907, baseEnd_2725907] using wordTrace_append hprefix tailTrace_2725907
  have hstable : (prefixWord ++ tailWord_2725907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725907).length < 2 ^ (prefixWord ++ tailWord_2725907).sum := by decide
  have hdescent : baseEnd_2725907 < baseStart_2725907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725999 : List Nat := [1, 1, 2, 1, 3, 4, 1, 2, 1, 6]
def baseStart_2725999 : Nat := 118140960795 + 2725999 * 2 ^ 59
def prefixEnd_2725999 : Nat := 4983230072969 + 3 ^ 40 * 2725999 * 2
def baseEnd_2725999 : Nat := 933165167117190166717243

theorem tailTrace_2725999 : CollatzResearch.WordTrace tailWord_2725999 prefixEnd_2725999 933165167117190166717243 := by
  unfold tailWord_2725999
  simp only [CollatzResearch.WordTrace]
  refine ⟨99425351651178661408901051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66283567767452440939267367 99425351651178661408901051)
  ·
    refine ⟨149138027476767992113351577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99425351651178661408901051 149138027476767992113351577)
    ·
      refine ⟨111853520607575994085013683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149138027476767992113351577 111853520607575994085013683)
      ·
        refine ⟨167780280911363991127520525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111853520607575994085013683 167780280911363991127520525)
        ·
          refine ⟨62917605341761496672820197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167780280911363991127520525 62917605341761496672820197)
          ·
            refine ⟨11797051001580280626153787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62917605341761496672820197 11797051001580280626153787)
            ·
              refine ⟨17695576502370420939230681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11797051001580280626153787 17695576502370420939230681)
              ·
                refine ⟨13271682376777815704423011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17695576502370420939230681 13271682376777815704423011)
                ·
                  refine ⟨19907523565166723556634517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13271682376777815704423011 19907523565166723556634517)
                  ·
                    refine ⟨933165167117190166717243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19907523565166723556634517 933165167117190166717243)
                    ·
                      rfl

theorem cell22_2725999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 6].length) (baseStart_2725999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2725999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2725999 prefixEnd_2725999 := by exact prefixLift 2725999
  have htrace : WordTrace (prefixWord ++ tailWord_2725999) baseStart_2725999 baseEnd_2725999 := by
    simpa [prefixWord, tailWord_2725999, baseEnd_2725999] using wordTrace_append hprefix tailTrace_2725999
  have hstable : (prefixWord ++ tailWord_2725999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725999).length < 2 ^ (prefixWord ++ tailWord_2725999).sum := by decide
  have hdescent : baseEnd_2725999 < baseStart_2725999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726052 : List Nat := [2, 3, 1, 2, 4, 2, 2, 1, 2, 3]
def baseStart_2726052 : Nat := 118140960795 + 2726052 * 2 ^ 59
def prefixEnd_2726052 : Nat := 4983230072969 + 3 ^ 40 * 2726052 * 2
def baseEnd_2726052 : Nat := 933183310100315695142081

theorem tailTrace_2726052 : CollatzResearch.WordTrace tailWord_2726052 prefixEnd_2726052 933183310100315695142081 := by
  unfold tailWord_2726052
  simp only [CollatzResearch.WordTrace]
  refine ⟨49713642359993325730290205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66284856479991100973720273 49713642359993325730290205)
  ·
    refine ⟨18642615884997497148858827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49713642359993325730290205 18642615884997497148858827)
    ·
      refine ⟨27963923827496245723288241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18642615884997497148858827 27963923827496245723288241)
      ·
        refine ⟨20972942870622184292466181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27963923827496245723288241 20972942870622184292466181)
        ·
          refine ⟨3932426788241659554837409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20972942870622184292466181 3932426788241659554837409)
          ·
            refine ⟨2949320091181244666128057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3932426788241659554837409 2949320091181244666128057)
            ·
              refine ⟨2211990068385933499596043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2949320091181244666128057 2211990068385933499596043)
              ·
                refine ⟨3317985102578900249394065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2211990068385933499596043 3317985102578900249394065)
                ·
                  refine ⟨2488488826934175187045549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3317985102578900249394065 2488488826934175187045549)
                  ·
                    refine ⟨933183310100315695142081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2488488826934175187045549 933183310100315695142081)
                    ·
                      rfl

theorem cell22_2726052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_2726052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726052 prefixEnd_2726052 := by exact prefixLift 2726052
  have htrace : WordTrace (prefixWord ++ tailWord_2726052) baseStart_2726052 baseEnd_2726052 := by
    simpa [prefixWord, tailWord_2726052, baseEnd_2726052] using wordTrace_append hprefix tailTrace_2726052
  have hstable : (prefixWord ++ tailWord_2726052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726052).length < 2 ^ (prefixWord ++ tailWord_2726052).sum := by decide
  have hdescent : baseEnd_2726052 < baseStart_2726052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726106 : List Nat := [3, 1, 1, 2, 2, 1, 3, 2, 3, 4]
def baseStart_2726106 : Nat := 118140960795 + 2726106 * 2 ^ 59
def prefixEnd_2726106 : Nat := 4983230072969 + 3 ^ 40 * 2726106 * 2
def baseEnd_2726106 : Nat := 933201795403877554291915

theorem tailTrace_2726106 : CollatzResearch.WordTrace tailWord_2726106 prefixEnd_2726106 933201795403877554291915 := by
  unfold tailWord_2726106
  simp only [CollatzResearch.WordTrace]
  refine ⟨24857313565447754670761543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66286169507860679122030781 24857313565447754670761543)
  ·
    refine ⟨37285970348171632006142315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24857313565447754670761543 37285970348171632006142315)
    ·
      refine ⟨55928955522257448009213473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37285970348171632006142315 55928955522257448009213473)
      ·
        refine ⟨41946716641693086006910105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55928955522257448009213473 41946716641693086006910105)
        ·
          refine ⟨31460037481269814505182579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41946716641693086006910105 31460037481269814505182579)
          ·
            refine ⟨47190056221904721757773869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31460037481269814505182579 47190056221904721757773869)
            ·
              refine ⟨17696271083214270659165201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47190056221904721757773869 17696271083214270659165201)
              ·
                refine ⟨13272203312410702994373901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17696271083214270659165201 13272203312410702994373901)
                ·
                  refine ⟨4977076242154013622890213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13272203312410702994373901 4977076242154013622890213)
                  ·
                    refine ⟨933201795403877554291915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4977076242154013622890213 933201795403877554291915)
                    ·
                      rfl

theorem cell22_2726106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_2726106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726106 prefixEnd_2726106 := by exact prefixLift 2726106
  have htrace : WordTrace (prefixWord ++ tailWord_2726106) baseStart_2726106 baseEnd_2726106 := by
    simpa [prefixWord, tailWord_2726106, baseEnd_2726106] using wordTrace_append hprefix tailTrace_2726106
  have hstable : (prefixWord ++ tailWord_2726106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726106).length < 2 ^ (prefixWord ++ tailWord_2726106).sum := by decide
  have hdescent : baseEnd_2726106 < baseStart_2726106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726114 : List Nat := [3, 3, 4, 1, 1, 1, 1, 2, 3, 3]
def baseStart_2726114 : Nat := 118140960795 + 2726114 * 2 ^ 59
def prefixEnd_2726114 : Nat := 4983230072969 + 3 ^ 40 * 2726114 * 2
def baseEnd_2726114 : Nat := 933204533967368200091891

theorem tailTrace_2726114 : CollatzResearch.WordTrace tailWord_2726114 prefixEnd_2726114 933204533967368200091891 := by
  unfold tailWord_2726114
  simp only [CollatzResearch.WordTrace]
  refine ⟨24857386511440509012334349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66286364030508024032891597 24857386511440509012334349)
  ·
    refine ⟨9321519941790190879625381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24857386511440509012334349 9321519941790190879625381)
    ·
      refine ⟨1747784989085660789929759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9321519941790190879625381 1747784989085660789929759)
      ·
        refine ⟨2621677483628491184894639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1747784989085660789929759 2621677483628491184894639)
        ·
          refine ⟨3932516225442736777341959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2621677483628491184894639 3932516225442736777341959)
          ·
            refine ⟨5898774338164105166012939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3932516225442736777341959 5898774338164105166012939)
            ·
              refine ⟨8848161507246157749019409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5898774338164105166012939 8848161507246157749019409)
              ·
                refine ⟨6636121130434618311764557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8848161507246157749019409 6636121130434618311764557)
                ·
                  refine ⟨2488545423912981866911709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6636121130434618311764557 2488545423912981866911709)
                  ·
                    refine ⟨933204533967368200091891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2488545423912981866911709 933204533967368200091891)
                    ·
                      rfl

theorem cell22_2726114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_2726114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726114 prefixEnd_2726114 := by exact prefixLift 2726114
  have htrace : WordTrace (prefixWord ++ tailWord_2726114) baseStart_2726114 baseEnd_2726114 := by
    simpa [prefixWord, tailWord_2726114, baseEnd_2726114] using wordTrace_append hprefix tailTrace_2726114
  have hstable : (prefixWord ++ tailWord_2726114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726114).length < 2 ^ (prefixWord ++ tailWord_2726114).sum := by decide
  have hdescent : baseEnd_2726114 < baseStart_2726114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726138 : List Nat := [3, 1, 1, 1, 1, 5, 1, 5, 4]
def baseStart_2726138 : Nat := 118140960795 + 2726138 * 2 ^ 59
def prefixEnd_2726138 : Nat := 4983230072969 + 3 ^ 40 * 2726138 * 2
def baseEnd_2726138 : Nat := 311070916552613379163939

theorem tailTrace_2726138 : CollatzResearch.WordTrace tailWord_2726138 prefixEnd_2726138 311070916552613379163939 := by
  unfold tailWord_2726138
  simp only [CollatzResearch.WordTrace]
  refine ⟨24857605349418772037052767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66286947598450058765474045 24857605349418772037052767)
  ·
    refine ⟨37286408024128158055579151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24857605349418772037052767 37286408024128158055579151)
    ·
      refine ⟨55929612036192237083368727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37286408024128158055579151 55929612036192237083368727)
      ·
        refine ⟨83894418054288355625053091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55929612036192237083368727 83894418054288355625053091)
        ·
          refine ⟨125841627081432533437579637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83894418054288355625053091 125841627081432533437579637)
          ·
            refine ⟨11797652538884300009773091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125841627081432533437579637 11797652538884300009773091)
            ·
              refine ⟨17696478808326450014659637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11797652538884300009773091 17696478808326450014659637)
              ·
                refine ⟨1659044888280604688874341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17696478808326450014659637 1659044888280604688874341)
                ·
                  refine ⟨311070916552613379163939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1659044888280604688874341 311070916552613379163939)
                  ·
                    rfl

theorem cell22_2726138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 5, 4].length) (baseStart_2726138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726138 prefixEnd_2726138 := by exact prefixLift 2726138
  have htrace : WordTrace (prefixWord ++ tailWord_2726138) baseStart_2726138 baseEnd_2726138 := by
    simpa [prefixWord, tailWord_2726138, baseEnd_2726138] using wordTrace_append hprefix tailTrace_2726138
  have hstable : (prefixWord ++ tailWord_2726138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726138).length < 2 ^ (prefixWord ++ tailWord_2726138).sum := by decide
  have hdescent : baseEnd_2726138 < baseStart_2726138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726140 : List Nat := [2, 2, 2, 1, 4, 1, 4, 1, 1, 4]
def baseStart_2726140 : Nat := 118140960795 + 2726140 * 2 ^ 59
def prefixEnd_2726140 : Nat := 4983230072969 + 3 ^ 40 * 2726140 * 2
def baseEnd_2726140 : Nat := 933213434298712798941811

theorem tailTrace_2726140 : CollatzResearch.WordTrace tailWord_2726140 prefixEnd_2726140 933213434298712798941811 := by
  unfold tailWord_2726140
  simp only [CollatzResearch.WordTrace]
  refine ⟨49715247171833921244891937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66286996229111894993189249 49715247171833921244891937)
  ·
    refine ⟨37286435378875440933668953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49715247171833921244891937 37286435378875440933668953)
    ·
      refine ⟨27964826534156580700251715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37286435378875440933668953 27964826534156580700251715)
      ·
        refine ⟨41947239801234871050377573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27964826534156580700251715 41947239801234871050377573)
        ·
          refine ⟨7865107462731538321945795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41947239801234871050377573 7865107462731538321945795)
          ·
            refine ⟨11797661194097307482918693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7865107462731538321945795 11797661194097307482918693)
            ·
              refine ⟨2212061473893245153047255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11797661194097307482918693 2212061473893245153047255)
              ·
                refine ⟨3318092210839867729570883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2212061473893245153047255 3318092210839867729570883)
                ·
                  refine ⟨4977138316259801594356325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3318092210839867729570883 4977138316259801594356325)
                  ·
                    refine ⟨933213434298712798941811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4977138316259801594356325 933213434298712798941811)
                    ·
                      rfl

theorem cell22_2726140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_2726140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726140 prefixEnd_2726140 := by exact prefixLift 2726140
  have htrace : WordTrace (prefixWord ++ tailWord_2726140) baseStart_2726140 baseEnd_2726140 := by
    simpa [prefixWord, tailWord_2726140, baseEnd_2726140] using wordTrace_append hprefix tailTrace_2726140
  have hstable : (prefixWord ++ tailWord_2726140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726140).length < 2 ^ (prefixWord ++ tailWord_2726140).sum := by decide
  have hdescent : baseEnd_2726140 < baseStart_2726140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726153 : List Nat := [1, 2, 1, 1, 3, 5, 1, 1, 4, 3]
def baseStart_2726153 : Nat := 118140960795 + 2726153 * 2 ^ 59
def prefixEnd_2726153 : Nat := 4983230072969 + 3 ^ 40 * 2726153 * 2
def baseEnd_2726153 : Nat := 933217884464385098366771

theorem tailTrace_2726153 : CollatzResearch.WordTrace tailWord_2726153 prefixEnd_2726153 933217884464385098366771 := by
  unfold tailWord_2726153
  simp only [CollatzResearch.WordTrace]
  refine ⟨99430968492620745710007113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66287312328413830473338075 99430968492620745710007113)
  ·
    refine ⟨74573226369465559282505335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99430968492620745710007113 74573226369465559282505335)
    ·
      refine ⟨111859839554198338923758003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74573226369465559282505335 111859839554198338923758003)
      ·
        refine ⟨167789759331297508385637005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111859839554198338923758003 167789759331297508385637005)
        ·
          refine ⟨62921159749236565644613877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167789759331297508385637005 62921159749236565644613877)
          ·
            refine ⟨5898858726490928029182551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62921159749236565644613877 5898858726490928029182551)
            ·
              refine ⟨8848288089736392043773827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5898858726490928029182551 8848288089736392043773827)
              ·
                refine ⟨13272432134604588065660741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8848288089736392043773827 13272432134604588065660741)
                ·
                  refine ⟨2488581025238360262311389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13272432134604588065660741 2488581025238360262311389)
                  ·
                    refine ⟨933217884464385098366771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2488581025238360262311389 933217884464385098366771)
                    ·
                      rfl

theorem cell22_2726153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 4, 3].length) (baseStart_2726153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726153 prefixEnd_2726153 := by exact prefixLift 2726153
  have htrace : WordTrace (prefixWord ++ tailWord_2726153) baseStart_2726153 baseEnd_2726153 := by
    simpa [prefixWord, tailWord_2726153, baseEnd_2726153] using wordTrace_append hprefix tailTrace_2726153
  have hstable : (prefixWord ++ tailWord_2726153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726153).length < 2 ^ (prefixWord ++ tailWord_2726153).sum := by decide
  have hdescent : baseEnd_2726153 < baseStart_2726153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726170 : List Nat := [3, 1, 1, 3, 4, 2, 1, 1, 1, 5]
def baseStart_2726170 : Nat := 118140960795 + 2726170 * 2 ^ 59
def prefixEnd_2726170 : Nat := 4983230072969 + 3 ^ 40 * 2726170 * 2
def baseEnd_2726170 : Nat := 933223703911802720691719

theorem tailTrace_2726170 : CollatzResearch.WordTrace tailWord_2726170 prefixEnd_2726170 933223703911802720691719 := by
  unfold tailWord_2726170
  simp only [CollatzResearch.WordTrace]
  refine ⟨24857897133389789403343991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66287725689039438408917309 24857897133389789403343991)
  ·
    refine ⟨37286845700084684105015987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24857897133389789403343991 37286845700084684105015987)
    ·
      refine ⟨55930268550127026157523981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37286845700084684105015987 55930268550127026157523981)
      ·
        refine ⟨20973850706297634809071493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55930268550127026157523981 20973850706297634809071493)
        ·
          refine ⟨3932597007430806526700905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20973850706297634809071493 3932597007430806526700905)
          ·
            refine ⟨2949447755573104895025679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3932597007430806526700905 2949447755573104895025679)
            ·
              refine ⟨4424171633359657342538519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2949447755573104895025679 4424171633359657342538519)
              ·
                refine ⟨6636257450039486013807779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4424171633359657342538519 6636257450039486013807779)
                ·
                  refine ⟨9954386175059229020711669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6636257450039486013807779 9954386175059229020711669)
                  ·
                    refine ⟨933223703911802720691719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9954386175059229020711669 933223703911802720691719)
                    ·
                      rfl

theorem cell22_2726170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 1, 5].length) (baseStart_2726170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726170 prefixEnd_2726170 := by exact prefixLift 2726170
  have htrace : WordTrace (prefixWord ++ tailWord_2726170) baseStart_2726170 baseEnd_2726170 := by
    simpa [prefixWord, tailWord_2726170, baseEnd_2726170] using wordTrace_append hprefix tailTrace_2726170
  have hstable : (prefixWord ++ tailWord_2726170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726170).length < 2 ^ (prefixWord ++ tailWord_2726170).sum := by decide
  have hdescent : baseEnd_2726170 < baseStart_2726170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726189 : List Nat := [1, 5, 3, 1, 2, 2, 1, 3, 4]
def baseStart_2726189 : Nat := 118140960795 + 2726189 * 2 ^ 59
def prefixEnd_2726189 : Nat := 4983230072969 + 3 ^ 40 * 2726189 * 2
def baseEnd_2726189 : Nat := 311076736000031001488887

theorem tailTrace_2726189 : CollatzResearch.WordTrace tailWord_2726189 prefixEnd_2726189 311076736000031001488887 := by
  unfold tailWord_2726189
  simp only [CollatzResearch.WordTrace]
  refine ⟨99432281520490323858317621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66288187680326882572211747 99432281520490323858317621)
  ·
    refine ⟨9321776392545967861717277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99432281520490323858317621 9321776392545967861717277)
    ·
      refine ⟨3495666147204737948143979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9321776392545967861717277 3495666147204737948143979)
      ·
        refine ⟨5243499220807106922215969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3495666147204737948143979 5243499220807106922215969)
        ·
          refine ⟨3932624415605330191661977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5243499220807106922215969 3932624415605330191661977)
          ·
            refine ⟨2949468311703997643746483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3932624415605330191661977 2949468311703997643746483)
            ·
              refine ⟨4424202467555996465619725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2949468311703997643746483 4424202467555996465619725)
              ·
                refine ⟨1659075925333498674607397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4424202467555996465619725 1659075925333498674607397)
                ·
                  refine ⟨311076736000031001488887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1659075925333498674607397 311076736000031001488887)
                  ·
                    rfl

theorem cell22_2726189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_2726189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726189 prefixEnd_2726189 := by exact prefixLift 2726189
  have htrace : WordTrace (prefixWord ++ tailWord_2726189) baseStart_2726189 baseEnd_2726189 := by
    simpa [prefixWord, tailWord_2726189, baseEnd_2726189] using wordTrace_append hprefix tailTrace_2726189
  have hstable : (prefixWord ++ tailWord_2726189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726189).length < 2 ^ (prefixWord ++ tailWord_2726189).sum := by decide
  have hdescent : baseEnd_2726189 < baseStart_2726189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726211 : List Nat := [1, 1, 1, 3, 1, 3, 4, 1, 7]
def baseStart_2726211 : Nat := 118140960795 + 2726211 * 2 ^ 59
def prefixEnd_2726211 : Nat := 4983230072969 + 3 ^ 40 * 2726211 * 2
def baseEnd_2726211 : Nat := 311079246349897426805531

theorem tailTrace_2726211 : CollatzResearch.WordTrace tailWord_2726211 prefixEnd_2726211 311079246349897426805531 := by
  unfold tailWord_2726211
  simp only [CollatzResearch.WordTrace]
  refine ⟨99433083926410621615618487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66288722617607081077078991 99433083926410621615618487)
  ·
    refine ⟨149149625889615932423427731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99433083926410621615618487 149149625889615932423427731)
    ·
      refine ⟨223724438834423898635141597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149149625889615932423427731 223724438834423898635141597)
      ·
        refine ⟨83896664562908961988178099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223724438834423898635141597 83896664562908961988178099)
        ·
          refine ⟨125844996844363442982267149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83896664562908961988178099 125844996844363442982267149)
          ·
            refine ⟨47191873816636291118350181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125844996844363442982267149 47191873816636291118350181)
            ·
              refine ⟨8848476340619304584690659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47191873816636291118350181 8848476340619304584690659)
              ·
                refine ⟨13272714510928956877035989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8848476340619304584690659 13272714510928956877035989)
                ·
                  refine ⟨311079246349897426805531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13272714510928956877035989 311079246349897426805531)
                  ·
                    rfl

theorem cell22_2726211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 7].length) (baseStart_2726211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726211 prefixEnd_2726211 := by exact prefixLift 2726211
  have htrace : WordTrace (prefixWord ++ tailWord_2726211) baseStart_2726211 baseEnd_2726211 := by
    simpa [prefixWord, tailWord_2726211, baseEnd_2726211] using wordTrace_append hprefix tailTrace_2726211
  have hstable : (prefixWord ++ tailWord_2726211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726211).length < 2 ^ (prefixWord ++ tailWord_2726211).sum := by decide
  have hdescent : baseEnd_2726211 < baseStart_2726211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726303 : List Nat := [1, 1, 2, 5, 1, 1, 3, 1, 1, 6]
def baseStart_2726303 : Nat := 118140960795 + 2726303 * 2 ^ 59
def prefixEnd_2726303 : Nat := 4983230072969 + 3 ^ 40 * 2726303 * 2
def baseEnd_2726303 : Nat := 933269232529834707116311

theorem tailTrace_2726303 : CollatzResearch.WordTrace tailWord_2726303 prefixEnd_2726303 933269232529834707116311 := by
  unfold tailWord_2726303
  simp only [CollatzResearch.WordTrace]
  refine ⟨99436439442077321327967563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66290959628051547551978375 99436439442077321327967563)
  ·
    refine ⟨149154659163115981991951345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99436439442077321327967563 149154659163115981991951345)
    ·
      refine ⟨111865994372336986493963509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149154659163115981991951345 111865994372336986493963509)
      ·
        refine ⟨10487436972406592483809079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111865994372336986493963509 10487436972406592483809079)
        ·
          refine ⟨15731155458609888725713619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10487436972406592483809079 15731155458609888725713619)
          ·
            refine ⟨23596733187914833088570429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15731155458609888725713619 23596733187914833088570429)
            ·
              refine ⟨8848774945468062408213911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23596733187914833088570429 8848774945468062408213911)
              ·
                refine ⟨13273162418202093612320867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8848774945468062408213911 13273162418202093612320867)
                ·
                  refine ⟨19909743627303140418481301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13273162418202093612320867 19909743627303140418481301)
                  ·
                    refine ⟨933269232529834707116311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19909743627303140418481301 933269232529834707116311)
                    ·
                      rfl

theorem cell22_2726303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 6].length) (baseStart_2726303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726303 prefixEnd_2726303 := by exact prefixLift 2726303
  have htrace : WordTrace (prefixWord ++ tailWord_2726303) baseStart_2726303 baseEnd_2726303 := by
    simpa [prefixWord, tailWord_2726303, baseEnd_2726303] using wordTrace_append hprefix tailTrace_2726303
  have hstable : (prefixWord ++ tailWord_2726303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726303).length < 2 ^ (prefixWord ++ tailWord_2726303).sum := by decide
  have hdescent : baseEnd_2726303 < baseStart_2726303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726324 : List Nat := [2, 5, 2, 2, 1, 1, 2, 1, 6]
def baseStart_2726324 : Nat := 118140960795 + 2726324 * 2 ^ 59
def prefixEnd_2726324 : Nat := 4983230072969 + 3 ^ 40 * 2726324 * 2
def baseEnd_2726324 : Nat := 311092140419665884113749

theorem tailTrace_2726324 : CollatzResearch.WordTrace tailWord_2726324 prefixEnd_2726324 311092140419665884113749 := by
  unfold tailWord_2726324
  simp only [CollatzResearch.WordTrace]
  refine ⟨49718602687500620957241013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66291470250000827942988017 49718602687500620957241013)
  ·
    refine ⟨4661119001953183214741345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49718602687500620957241013 4661119001953183214741345)
    ·
      refine ⟨3495839251464887411056009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4661119001953183214741345 3495839251464887411056009)
      ·
        refine ⟨2621879438598665558292007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3495839251464887411056009 2621879438598665558292007)
        ·
          refine ⟨3932819157897998337438011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2621879438598665558292007 3932819157897998337438011)
          ·
            refine ⟨5899228736846997506157017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3932819157897998337438011 5899228736846997506157017)
            ·
              refine ⟨4424421552635248129617763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5899228736846997506157017 4424421552635248129617763)
              ·
                refine ⟨6636632328952872194426645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4424421552635248129617763 6636632328952872194426645)
                ·
                  refine ⟨311092140419665884113749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6636632328952872194426645 311092140419665884113749)
                  ·
                    rfl

theorem cell22_2726324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_2726324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726324 prefixEnd_2726324 := by exact prefixLift 2726324
  have htrace : WordTrace (prefixWord ++ tailWord_2726324) baseStart_2726324 baseEnd_2726324 := by
    simpa [prefixWord, tailWord_2726324, baseEnd_2726324] using wordTrace_append hprefix tailTrace_2726324
  have hstable : (prefixWord ++ tailWord_2726324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726324).length < 2 ^ (prefixWord ++ tailWord_2726324).sum := by decide
  have hdescent : baseEnd_2726324 < baseStart_2726324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726384 : List Nat := [2, 1, 1, 1, 3, 3, 5, 2, 1, 3]
def baseStart_2726384 : Nat := 118140960795 + 2726384 * 2 ^ 59
def prefixEnd_2726384 : Nat := 4983230072969 + 3 ^ 40 * 2726384 * 2
def baseEnd_2726384 : Nat := 933296960485177495841063

theorem tailTrace_2726384 : CollatzResearch.WordTrace tailWord_2726384 prefixEnd_2726384 933296960485177495841063 := by
  unfold tailWord_2726384
  simp only [CollatzResearch.WordTrace]
  refine ⟨49719696877391936080833103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66292929169855914774444137 49719696877391936080833103)
  ·
    refine ⟨74579545316087904121249655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49719696877391936080833103 74579545316087904121249655)
    ·
      refine ⟨111869317974131856181874483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74579545316087904121249655 111869317974131856181874483)
      ·
        refine ⟨167803976961197784272811725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111869317974131856181874483 167803976961197784272811725)
        ·
          refine ⟨62926491360449169102304397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167803976961197784272811725 62926491360449169102304397)
          ·
            refine ⟨23597434260168438413364149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62926491360449169102304397 23597434260168438413364149)
            ·
              refine ⟨2212259461890791101252889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23597434260168438413364149 2212259461890791101252889)
              ·
                refine ⟨1659194596418093325939667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2212259461890791101252889 1659194596418093325939667)
                ·
                  refine ⟨2488791894627139988909501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1659194596418093325939667 2488791894627139988909501)
                  ·
                    refine ⟨933296960485177495841063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2488791894627139988909501 933296960485177495841063)
                    ·
                      rfl

theorem cell22_2726384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 2, 1, 3].length) (baseStart_2726384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726384 prefixEnd_2726384 := by exact prefixLift 2726384
  have htrace : WordTrace (prefixWord ++ tailWord_2726384) baseStart_2726384 baseEnd_2726384 := by
    simpa [prefixWord, tailWord_2726384, baseEnd_2726384] using wordTrace_append hprefix tailTrace_2726384
  have hstable : (prefixWord ++ tailWord_2726384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726384).length < 2 ^ (prefixWord ++ tailWord_2726384).sum := by decide
  have hdescent : baseEnd_2726384 < baseStart_2726384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726408 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 8]
def baseStart_2726408 : Nat := 118140960795 + 2726408 * 2 ^ 59
def prefixEnd_2726408 : Nat := 4983230072969 + 3 ^ 40 * 2726408 * 2
def baseEnd_2726408 : Nat := 311101725391883144413663

theorem tailTrace_2726408 : CollatzResearch.WordTrace tailWord_2726408 prefixEnd_2726408 311101725391883144413663 := by
  unfold tailWord_2726408
  simp only [CollatzResearch.WordTrace]
  refine ⟨49720134553348462130269939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66293512737797949507026585 49720134553348462130269939)
  ·
    refine ⟨74580201830022693195404909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49720134553348462130269939 74580201830022693195404909)
    ·
      refine ⟨27967575686258509948276841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74580201830022693195404909 27967575686258509948276841)
      ·
        refine ⟨20975681764693882461207631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27967575686258509948276841 20975681764693882461207631)
        ·
          refine ⟨31463522647040823691811447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20975681764693882461207631 31463522647040823691811447)
          ·
            refine ⟨47195283970561235537717171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31463522647040823691811447 47195283970561235537717171)
            ·
              refine ⟨70792925955841853306575757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47195283970561235537717171 70792925955841853306575757)
              ·
                refine ⟨26547347233440694989965909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70792925955841853306575757 26547347233440694989965909)
                ·
                  refine ⟨311101725391883144413663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26547347233440694989965909 311101725391883144413663)
                  ·
                    rfl

theorem cell22_2726408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 8].length) (baseStart_2726408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726408 prefixEnd_2726408 := by exact prefixLift 2726408
  have htrace : WordTrace (prefixWord ++ tailWord_2726408) baseStart_2726408 baseEnd_2726408 := by
    simpa [prefixWord, tailWord_2726408, baseEnd_2726408] using wordTrace_append hprefix tailTrace_2726408
  have hstable : (prefixWord ++ tailWord_2726408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726408).length < 2 ^ (prefixWord ++ tailWord_2726408).sum := by decide
  have hdescent : baseEnd_2726408 < baseStart_2726408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726410 : List Nat := [3, 1, 2, 2, 2, 1, 3, 1, 3, 4]
def baseStart_2726410 : Nat := 118140960795 + 2726410 * 2 ^ 59
def prefixEnd_2726410 : Nat := 4983230072969 + 3 ^ 40 * 2726410 * 2
def baseEnd_2726410 : Nat := 933305860816522094690983

theorem tailTrace_2726410 : CollatzResearch.WordTrace tailWord_2726410 prefixEnd_2726410 933305860816522094690983 := by
  unfold tailWord_2726410
  simp only [CollatzResearch.WordTrace]
  refine ⟨24860085513172419650528171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66293561368459785734741789 24860085513172419650528171)
  ·
    refine ⟨37290128269758629475792257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24860085513172419650528171 37290128269758629475792257)
    ·
      refine ⟨27967596202318972106844193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37290128269758629475792257 27967596202318972106844193)
      ·
        refine ⟨20975697151739229080133145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27967596202318972106844193 20975697151739229080133145)
        ·
          refine ⟨15731772863804421810099859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20975697151739229080133145 15731772863804421810099859)
          ·
            refine ⟨23597659295706632715149789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15731772863804421810099859 23597659295706632715149789)
            ·
              refine ⟨8849122235889987268181171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23597659295706632715149789 8849122235889987268181171)
              ·
                refine ⟨13273683353834980902271757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8849122235889987268181171 13273683353834980902271757)
                ·
                  refine ⟨4977631257688117838351909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13273683353834980902271757 4977631257688117838351909)
                  ·
                    refine ⟨933305860816522094690983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4977631257688117838351909 933305860816522094690983)
                    ·
                      rfl

theorem cell22_2726410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_2726410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726410 prefixEnd_2726410 := by exact prefixLift 2726410
  have htrace : WordTrace (prefixWord ++ tailWord_2726410) baseStart_2726410 baseEnd_2726410 := by
    simpa [prefixWord, tailWord_2726410, baseEnd_2726410] using wordTrace_append hprefix tailTrace_2726410
  have hstable : (prefixWord ++ tailWord_2726410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726410).length < 2 ^ (prefixWord ++ tailWord_2726410).sum := by decide
  have hdescent : baseEnd_2726410 < baseStart_2726410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726457 : List Nat := [1, 2, 1, 5, 1, 1, 1, 5, 2, 3]
def baseStart_2726457 : Nat := 118140960795 + 2726457 * 2 ^ 59
def prefixEnd_2726457 : Nat := 4983230072969 + 3 ^ 40 * 2726457 * 2
def baseEnd_2726457 : Nat := 933321949877029638765839

theorem tailTrace_2726457 : CollatzResearch.WordTrace tailWord_2726457 prefixEnd_2726457 933321949877029638765839 := by
  unfold tailWord_2726457
  simp only [CollatzResearch.WordTrace]
  refine ⟨99442056283519405629073625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66294704189012937086049083 99442056283519405629073625)
  ·
    refine ⟨74581542212639554221805219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99442056283519405629073625 74581542212639554221805219)
    ·
      refine ⟨111872313318959331332707829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74581542212639554221805219 111872313318959331332707829)
      ·
        refine ⟨10488029373652437312441359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111872313318959331332707829 10488029373652437312441359)
        ·
          refine ⟨15732044060478655968662039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10488029373652437312441359 15732044060478655968662039)
          ·
            refine ⟨23598066090717983952993059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15732044060478655968662039 23598066090717983952993059)
            ·
              refine ⟨35397099136076975929489589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23598066090717983952993059 35397099136076975929489589)
              ·
                refine ⟨3318478044007216493389649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35397099136076975929489589 3318478044007216493389649)
                ·
                  refine ⟨2488858533005412370042237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3318478044007216493389649 2488858533005412370042237)
                  ·
                    refine ⟨933321949877029638765839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2488858533005412370042237 933321949877029638765839)
                    ·
                      rfl

theorem cell22_2726457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 2, 3].length) (baseStart_2726457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726457 prefixEnd_2726457 := by exact prefixLift 2726457
  have htrace : WordTrace (prefixWord ++ tailWord_2726457) baseStart_2726457 baseEnd_2726457 := by
    simpa [prefixWord, tailWord_2726457, baseEnd_2726457] using wordTrace_append hprefix tailTrace_2726457
  have hstable : (prefixWord ++ tailWord_2726457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726457).length < 2 ^ (prefixWord ++ tailWord_2726457).sum := by decide
  have hdescent : baseEnd_2726457 < baseStart_2726457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726579 : List Nat := [1, 1, 1, 2, 3, 6, 1, 2, 1, 4]
def baseStart_2726579 : Nat := 118140960795 + 2726579 * 2 ^ 59
def prefixEnd_2726579 : Nat := 4983230072969 + 3 ^ 40 * 2726579 * 2
def baseEnd_2726579 : Nat := 933363712970261987215465

theorem tailTrace_2726579 : CollatzResearch.WordTrace tailWord_2726579 prefixEnd_2726579 933363712970261987215465 := by
  unfold tailWord_2726579
  simp only [CollatzResearch.WordTrace]
  refine ⟨99446505989077420465014791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66297670659384946976676527 99446505989077420465014791)
  ·
    refine ⟨149169758983616130697522187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99446505989077420465014791 149169758983616130697522187)
    ·
      refine ⟨223754638475424196046283281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149169758983616130697522187 223754638475424196046283281)
      ·
        refine ⟨167815978856568147034712461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223754638475424196046283281 167815978856568147034712461)
        ·
          refine ⟨62930992071213055138017173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167815978856568147034712461 62930992071213055138017173)
          ·
            refine ⟨2949890253338111959594555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62930992071213055138017173 2949890253338111959594555)
            ·
              refine ⟨4424835380007167939391833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2949890253338111959594555 4424835380007167939391833)
              ·
                refine ⟨3318626535005375954543875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4424835380007167939391833 3318626535005375954543875)
                ·
                  refine ⟨4977939802508063931815813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3318626535005375954543875 4977939802508063931815813)
                  ·
                    refine ⟨933363712970261987215465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4977939802508063931815813 933363712970261987215465)
                    ·
                      rfl

theorem cell22_2726579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 4].length) (baseStart_2726579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726579 prefixEnd_2726579 := by exact prefixLift 2726579
  have htrace : WordTrace (prefixWord ++ tailWord_2726579) baseStart_2726579 baseEnd_2726579 := by
    simpa [prefixWord, tailWord_2726579, baseEnd_2726579] using wordTrace_append hprefix tailTrace_2726579
  have hstable : (prefixWord ++ tailWord_2726579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726579).length < 2 ^ (prefixWord ++ tailWord_2726579).sum := by decide
  have hdescent : baseEnd_2726579 < baseStart_2726579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726592 : List Nat := [2, 1, 1, 2, 4, 3, 1, 2, 1, 5]
def baseStart_2726592 : Nat := 118140960795 + 2726592 * 2 ^ 59
def prefixEnd_2726592 : Nat := 4983230072969 + 3 ^ 40 * 2726592 * 2
def baseEnd_2726592 : Nat := 933368163135934286640425

theorem tailTrace_2726592 : CollatzResearch.WordTrace tailWord_2726592 prefixEnd_2726592 933368163135934286640425 := by
  unfold tailWord_2726592
  simp only [CollatzResearch.WordTrace]
  refine ⟨49723490069015161842619015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66297986758686882456825353 49723490069015161842619015)
  ·
    refine ⟨74585235103522742763928523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49723490069015161842619015 74585235103522742763928523)
    ·
      refine ⟨111877852655284114145892785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74585235103522742763928523 111877852655284114145892785)
      ·
        refine ⟨83908389491463085609419589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111877852655284114145892785 83908389491463085609419589)
        ·
          refine ⟨15732823029649328551766173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83908389491463085609419589 15732823029649328551766173)
          ·
            refine ⟨5899808636118498206912315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15732823029649328551766173 5899808636118498206912315)
            ·
              refine ⟨8849712954177747310368473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5899808636118498206912315 8849712954177747310368473)
              ·
                refine ⟨6637284715633310482776355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8849712954177747310368473 6637284715633310482776355)
                ·
                  refine ⟨9955927073449965724164533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6637284715633310482776355 9955927073449965724164533)
                  ·
                    refine ⟨933368163135934286640425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9955927073449965724164533 933368163135934286640425)
                    ·
                      rfl

theorem cell22_2726592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 1, 5].length) (baseStart_2726592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726592 prefixEnd_2726592 := by exact prefixLift 2726592
  have htrace : WordTrace (prefixWord ++ tailWord_2726592) baseStart_2726592 baseEnd_2726592 := by
    simpa [prefixWord, tailWord_2726592, baseEnd_2726592] using wordTrace_append hprefix tailTrace_2726592
  have hstable : (prefixWord ++ tailWord_2726592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726592).length < 2 ^ (prefixWord ++ tailWord_2726592).sum := by decide
  have hdescent : baseEnd_2726592 < baseStart_2726592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726596 : List Nat := [2, 3, 3, 1, 1, 3, 3, 1, 1, 4]
def baseStart_2726596 : Nat := 118140960795 + 2726596 * 2 ^ 59
def prefixEnd_2726596 : Nat := 4983230072969 + 3 ^ 40 * 2726596 * 2
def baseEnd_2726596 : Nat := 933369532417679609540413

theorem tailTrace_2726596 : CollatzResearch.WordTrace tailWord_2726596 prefixEnd_2726596 933369532417679609540413 := by
  unfold tailWord_2726596
  simp only [CollatzResearch.WordTrace]
  refine ⟨49723563015007916184191821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66298084020010554912255761 49723563015007916184191821)
  ·
    refine ⟨18646336130627968569071933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49723563015007916184191821 18646336130627968569071933)
    ·
      refine ⟨6992376048985488213401975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18646336130627968569071933 6992376048985488213401975)
      ·
        refine ⟨10488564073478232320102963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6992376048985488213401975 10488564073478232320102963)
        ·
          refine ⟨15732846110217348480154445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10488564073478232320102963 15732846110217348480154445)
          ·
            refine ⟨5899817291331505680057917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15732846110217348480154445 5899817291331505680057917)
            ·
              refine ⟨2212431484249314630021719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5899817291331505680057917 2212431484249314630021719)
              ·
                refine ⟨3318647226373971945032579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2212431484249314630021719 3318647226373971945032579)
                ·
                  refine ⟨4977970839560957917548869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3318647226373971945032579 4977970839560957917548869)
                  ·
                    refine ⟨933369532417679609540413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4977970839560957917548869 933369532417679609540413)
                    ·
                      rfl

theorem cell22_2726596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_2726596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726596 prefixEnd_2726596 := by exact prefixLift 2726596
  have htrace : WordTrace (prefixWord ++ tailWord_2726596) baseStart_2726596 baseEnd_2726596 := by
    simpa [prefixWord, tailWord_2726596, baseEnd_2726596] using wordTrace_append hprefix tailTrace_2726596
  have hstable : (prefixWord ++ tailWord_2726596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726596).length < 2 ^ (prefixWord ++ tailWord_2726596).sum := by decide
  have hdescent : baseEnd_2726596 < baseStart_2726596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726609 : List Nat := [1, 2, 2, 1, 2, 3, 4, 2, 2, 3]
def baseStart_2726609 : Nat := 118140960795 + 2726609 * 2 ^ 59
def prefixEnd_2726609 : Nat := 4983230072969 + 3 ^ 40 * 2726609 * 2
def baseEnd_2726609 : Nat := 933373982583351908965373

theorem tailTrace_2726609 : CollatzResearch.WordTrace tailWord_2726609 prefixEnd_2726609 933373982583351908965373 := by
  unfold tailWord_2726609
  simp only [CollatzResearch.WordTrace]
  refine ⟨99447600178968735588606881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66298400119312490392404587 99447600178968735588606881)
  ·
    refine ⟨74585700134226551691455161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99447600178968735588606881 74585700134226551691455161)
    ·
      refine ⟨55939275100669913768591371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74585700134226551691455161 55939275100669913768591371)
      ·
        refine ⟨83908912651004870652887057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55939275100669913768591371 83908912651004870652887057)
        ·
          refine ⟨62931684488253652989665293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83908912651004870652887057 62931684488253652989665293)
          ·
            refine ⟨23599381683095119871124485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62931684488253652989665293 23599381683095119871124485)
            ·
              refine ⟨4424884065580334975835841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23599381683095119871124485 4424884065580334975835841)
              ·
                refine ⟨3318663049185251231876881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4424884065580334975835841 3318663049185251231876881)
                ·
                  refine ⟨2488997286888938423907661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3318663049185251231876881 2488997286888938423907661)
                  ·
                    refine ⟨933373982583351908965373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2488997286888938423907661 933373982583351908965373)
                    ·
                      rfl

theorem cell22_2726609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 2, 3].length) (baseStart_2726609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726609 prefixEnd_2726609 := by exact prefixLift 2726609
  have htrace : WordTrace (prefixWord ++ tailWord_2726609) baseStart_2726609 baseEnd_2726609 := by
    simpa [prefixWord, tailWord_2726609, baseEnd_2726609] using wordTrace_append hprefix tailTrace_2726609
  have hstable : (prefixWord ++ tailWord_2726609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726609).length < 2 ^ (prefixWord ++ tailWord_2726609).sum := by decide
  have hdescent : baseEnd_2726609 < baseStart_2726609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726635 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 4, 6]
def baseStart_2726635 : Nat := 118140960795 + 2726635 * 2 ^ 59
def prefixEnd_2726635 : Nat := 4983230072969 + 3 ^ 40 * 2726635 * 2
def baseEnd_2726635 : Nat := 933382882914696507815293

theorem tailTrace_2726635 : CollatzResearch.WordTrace tailWord_2726635 prefixEnd_2726635 933382882914696507815293 := by
  unfold tailWord_2726635
  simp only [CollatzResearch.WordTrace]
  refine ⟨99448548476874542029053359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66299032317916361352702239 99448548476874542029053359)
  ·
    refine ⟨149172822715311813043580039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99448548476874542029053359 149172822715311813043580039)
    ·
      refine ⟨223759234072967719565370059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149172822715311813043580039 223759234072967719565370059)
      ·
        refine ⟨335638851109451579348055089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223759234072967719565370059 335638851109451579348055089)
        ·
          refine ⟨251729138332088684511041317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335638851109451579348055089 251729138332088684511041317)
          ·
            refine ⟨47199213437266628345820247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 251729138332088684511041317 47199213437266628345820247)
            ·
              refine ⟨70798820155899942518730371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47199213437266628345820247 70798820155899942518730371)
              ·
                refine ⟨106198230233849913778095557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70798820155899942518730371 106198230233849913778095557)
                ·
                  refine ⟨19912168168846858833392917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106198230233849913778095557 19912168168846858833392917)
                  ·
                    refine ⟨933382882914696507815293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19912168168846858833392917 933382882914696507815293)
                    ·
                      rfl

theorem cell22_2726635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 6].length) (baseStart_2726635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726635 prefixEnd_2726635 := by exact prefixLift 2726635
  have htrace : WordTrace (prefixWord ++ tailWord_2726635) baseStart_2726635 baseEnd_2726635 := by
    simpa [prefixWord, tailWord_2726635, baseEnd_2726635] using wordTrace_append hprefix tailTrace_2726635
  have hstable : (prefixWord ++ tailWord_2726635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726635).length < 2 ^ (prefixWord ++ tailWord_2726635).sum := by decide
  have hdescent : baseEnd_2726635 < baseStart_2726635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726645 : List Nat := [1, 3, 6, 1, 1, 1, 2, 3, 4]
def baseStart_2726645 : Nat := 118140960795 + 2726645 * 2 ^ 59
def prefixEnd_2726645 : Nat := 4983230072969 + 3 ^ 40 * 2726645 * 2
def baseEnd_2726645 : Nat := 311128768706353271688421

theorem tailTrace_2726645 : CollatzResearch.WordTrace tailWord_2726645 prefixEnd_2726645 311128768706353271688421 := by
  unfold tailWord_2726645
  simp only [CollatzResearch.WordTrace]
  refine ⟨99448913206838313736917389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66299275471225542491278259 99448913206838313736917389)
  ·
    refine ⟨37293342452564367651344021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99448913206838313736917389 37293342452564367651344021)
    ·
      refine ⟨1748125427463954733656751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 37293342452564367651344021 1748125427463954733656751)
      ·
        refine ⟨2622188141195932100485127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1748125427463954733656751 2622188141195932100485127)
        ·
          refine ⟨3933282211793898150727691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2622188141195932100485127 3933282211793898150727691)
          ·
            refine ⟨5899923317690847226091537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3933282211793898150727691 5899923317690847226091537)
            ·
              refine ⟨4424942488268135419568653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5899923317690847226091537 4424942488268135419568653)
              ·
                refine ⟨1659353433100550782338245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4424942488268135419568653 1659353433100550782338245)
                ·
                  refine ⟨311128768706353271688421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1659353433100550782338245 311128768706353271688421)
                  ·
                    rfl

theorem cell22_2726645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 3, 4].length) (baseStart_2726645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726645 prefixEnd_2726645 := by exact prefixLift 2726645
  have htrace : WordTrace (prefixWord ++ tailWord_2726645) baseStart_2726645 baseEnd_2726645 := by
    simpa [prefixWord, tailWord_2726645, baseEnd_2726645] using wordTrace_append hprefix tailTrace_2726645
  have hstable : (prefixWord ++ tailWord_2726645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726645).length < 2 ^ (prefixWord ++ tailWord_2726645).sum := by decide
  have hdescent : baseEnd_2726645 < baseStart_2726645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726682 : List Nat := [3, 1, 1, 3, 2, 1, 1, 3, 2, 5]
def baseStart_2726682 : Nat := 118140960795 + 2726682 * 2 ^ 59
def prefixEnd_2726682 : Nat := 4983230072969 + 3 ^ 40 * 2726682 * 2
def baseEnd_2726682 : Nat := 933398971975204051890149

theorem tailTrace_2726682 : CollatzResearch.WordTrace tailWord_2726682 prefixEnd_2726682 933398971975204051890149 := by
  unfold tailWord_2726682
  simp only [CollatzResearch.WordTrace]
  refine ⟨24862565676926067264003575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66300175138469512704009533 24862565676926067264003575)
  ·
    refine ⟨37293848515389100896005363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24862565676926067264003575 37293848515389100896005363)
    ·
      refine ⟨55940772773083651344008045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37293848515389100896005363 55940772773083651344008045)
      ·
        refine ⟨20977789789906369254003017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55940772773083651344008045 20977789789906369254003017)
        ·
          refine ⟨15733342342429776940502263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20977789789906369254003017 15733342342429776940502263)
          ·
            refine ⟨23600013513644665410753395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15733342342429776940502263 23600013513644665410753395)
            ·
              refine ⟨35400020270466998116130093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23600013513644665410753395 35400020270466998116130093)
              ·
                refine ⟨13275007601425124293548785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35400020270466998116130093 13275007601425124293548785)
                ·
                  refine ⟨9956255701068843220161589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13275007601425124293548785 9956255701068843220161589)
                  ·
                    refine ⟨933398971975204051890149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9956255701068843220161589 933398971975204051890149)
                    ·
                      rfl

theorem cell22_2726682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_2726682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726682 prefixEnd_2726682 := by exact prefixLift 2726682
  have htrace : WordTrace (prefixWord ++ tailWord_2726682) baseStart_2726682 baseEnd_2726682 := by
    simpa [prefixWord, tailWord_2726682, baseEnd_2726682] using wordTrace_append hprefix tailTrace_2726682
  have hstable : (prefixWord ++ tailWord_2726682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726682).length < 2 ^ (prefixWord ++ tailWord_2726682).sum := by decide
  have hdescent : baseEnd_2726682 < baseStart_2726682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726729 : List Nat := [1, 2, 1, 1, 2, 7, 1, 1, 6]
def baseStart_2726729 : Nat := 118140960795 + 2726729 * 2 ^ 59
def prefixEnd_2726729 : Nat := 4983230072969 + 3 ^ 40 * 2726729 * 2
def baseEnd_2726729 : Nat := 311138353678570531988335

theorem tailTrace_2726729 : CollatzResearch.WordTrace tailWord_2726729 prefixEnd_2726729 311138353678570531988335 := by
  unfold tailWord_2726729
  simp only [CollatzResearch.WordTrace]
  refine ⟨99451976938533996082975241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66301317959022664055316827 99451976938533996082975241)
  ·
    refine ⟨74588982703900497062231431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99451976938533996082975241 74588982703900497062231431)
    ·
      refine ⟨111883474055850745593347147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74588982703900497062231431 111883474055850745593347147)
      ·
        refine ⟨167825211083776118390020721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111883474055850745593347147 167825211083776118390020721)
        ·
          refine ⟨125868908312832088792515541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167825211083776118390020721 125868908312832088792515541)
          ·
            refine ⟨2950052538582002081074583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 125868908312832088792515541 2950052538582002081074583)
            ·
              refine ⟨4425078807873003121611875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2950052538582002081074583 4425078807873003121611875)
              ·
                refine ⟨6637618211809504682417813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4425078807873003121611875 6637618211809504682417813)
                ·
                  refine ⟨311138353678570531988335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6637618211809504682417813 311138353678570531988335)
                  ·
                    rfl

theorem cell22_2726729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 6].length) (baseStart_2726729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726729 prefixEnd_2726729 := by exact prefixLift 2726729
  have htrace : WordTrace (prefixWord ++ tailWord_2726729) baseStart_2726729 baseEnd_2726729 := by
    simpa [prefixWord, tailWord_2726729, baseEnd_2726729] using wordTrace_append hprefix tailTrace_2726729
  have hstable : (prefixWord ++ tailWord_2726729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726729).length < 2 ^ (prefixWord ++ tailWord_2726729).sum := by decide
  have hdescent : baseEnd_2726729 < baseStart_2726729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726748 : List Nat := [2, 2, 4, 2, 1, 3, 1, 2, 1, 4]
def baseStart_2726748 : Nat := 118140960795 + 2726748 * 2 ^ 59
def prefixEnd_2726748 : Nat := 4983230072969 + 3 ^ 40 * 2726748 * 2
def baseEnd_2726748 : Nat := 933421565124001879739947

theorem tailTrace_2726748 : CollatzResearch.WordTrace tailWord_2726748 prefixEnd_2726748 933421565124001879739947 := by
  unfold tailWord_2726748
  simp only [CollatzResearch.WordTrace]
  refine ⟨49726334962732581163958449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66301779950310108218611265 49726334962732581163958449)
  ·
    refine ⟨37294751222049435872968837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49726334962732581163958449 37294751222049435872968837)
    ·
      refine ⟨6992765854134269226181657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37294751222049435872968837 6992765854134269226181657)
      ·
        refine ⟨5244574390600701919636243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6992765854134269226181657 5244574390600701919636243)
        ·
          refine ⟨7866861585901052879454365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5244574390600701919636243 7866861585901052879454365)
          ·
            refine ⟨2950073094712894829795387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7866861585901052879454365 2950073094712894829795387)
            ·
              refine ⟨4425109642069342244693081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2950073094712894829795387 4425109642069342244693081)
              ·
                refine ⟨3318832231552006683519811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4425109642069342244693081 3318832231552006683519811)
                ·
                  refine ⟨4978248347328010025279717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3318832231552006683519811 4978248347328010025279717)
                  ·
                    refine ⟨933421565124001879739947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4978248347328010025279717 933421565124001879739947)
                    ·
                      rfl

theorem cell22_2726748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_2726748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726748 prefixEnd_2726748 := by exact prefixLift 2726748
  have htrace : WordTrace (prefixWord ++ tailWord_2726748) baseStart_2726748 baseEnd_2726748 := by
    simpa [prefixWord, tailWord_2726748, baseEnd_2726748] using wordTrace_append hprefix tailTrace_2726748
  have hstable : (prefixWord ++ tailWord_2726748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726748).length < 2 ^ (prefixWord ++ tailWord_2726748).sum := by decide
  have hdescent : baseEnd_2726748 < baseStart_2726748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726757 : List Nat := [1, 3, 1, 3, 1, 1, 4, 8]
def baseStart_2726757 : Nat := 118140960795 + 2726757 * 2 ^ 59
def prefixEnd_2726757 : Nat := 4983230072969 + 3 ^ 40 * 2726757 * 2
def baseEnd_2726757 : Nat := 103713849556436539584991

theorem tailTrace_2726757 : CollatzResearch.WordTrace tailWord_2726757 prefixEnd_2726757 103713849556436539584991 := by
  unfold tailWord_2726757
  simp only [CollatzResearch.WordTrace]
  refine ⟨99452998182432556864994525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66301998788288371243329683 99452998182432556864994525)
  ·
    refine ⟨37294874318412208824372947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99452998182432556864994525 37294874318412208824372947)
    ·
      refine ⟨55942311477618313236559421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37294874318412208824372947 55942311477618313236559421)
      ·
        refine ⟨20978366804106867463709783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55942311477618313236559421 20978366804106867463709783)
        ·
          refine ⟨31467550206160301195564675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20978366804106867463709783 31467550206160301195564675)
          ·
            refine ⟨47201325309240451793347013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31467550206160301195564675 47201325309240451793347013)
            ·
              refine ⟨8850248495482584711252565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47201325309240451793347013 8850248495482584711252565)
              ·
                refine ⟨103713849556436539584991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8850248495482584711252565 103713849556436539584991)
                ·
                  rfl

theorem cell22_2726757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 8].length) (baseStart_2726757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726757 prefixEnd_2726757 := by exact prefixLift 2726757
  have htrace : WordTrace (prefixWord ++ tailWord_2726757) baseStart_2726757 baseEnd_2726757 := by
    simpa [prefixWord, tailWord_2726757, baseEnd_2726757] using wordTrace_append hprefix tailTrace_2726757
  have hstable : (prefixWord ++ tailWord_2726757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726757).length < 2 ^ (prefixWord ++ tailWord_2726757).sum := by decide
  have hdescent : baseEnd_2726757 < baseStart_2726757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726759 : List Nat := [1, 1, 5, 1, 2, 2, 1, 3, 2, 4]
def baseStart_2726759 : Nat := 118140960795 + 2726759 * 2 ^ 59
def prefixEnd_2726759 : Nat := 4983230072969 + 3 ^ 40 * 2726759 * 2
def baseEnd_2726759 : Nat := 933425330648801517714913

theorem tailTrace_2726759 : CollatzResearch.WordTrace tailWord_2726759 prefixEnd_2726759 933425330648801517714913 := by
  unfold tailWord_2726759
  simp only [CollatzResearch.WordTrace]
  refine ⟨99453071128425311206567331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66302047418950207471044887 99453071128425311206567331)
  ·
    refine ⟨149179606692637966809850997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99453071128425311206567331 149179606692637966809850997)
    ·
      refine ⟨13985588127434809388423531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 149179606692637966809850997 13985588127434809388423531)
      ·
        refine ⟨20978382191152214082635297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13985588127434809388423531 20978382191152214082635297)
        ·
          refine ⟨15733786643364160561976473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20978382191152214082635297 15733786643364160561976473)
          ·
            refine ⟨11800339982523120421482355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15733786643364160561976473 11800339982523120421482355)
            ·
              refine ⟨17700509973784680632223533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11800339982523120421482355 17700509973784680632223533)
              ·
                refine ⟨6637691240169255237083825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17700509973784680632223533 6637691240169255237083825)
                ·
                  refine ⟨4978268430126941427812869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6637691240169255237083825 4978268430126941427812869)
                  ·
                    refine ⟨933425330648801517714913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4978268430126941427812869 933425330648801517714913)
                    ·
                      rfl

theorem cell22_2726759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_2726759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726759 prefixEnd_2726759 := by exact prefixLift 2726759
  have htrace : WordTrace (prefixWord ++ tailWord_2726759) baseStart_2726759 baseEnd_2726759 := by
    simpa [prefixWord, tailWord_2726759, baseEnd_2726759] using wordTrace_append hprefix tailTrace_2726759
  have hstable : (prefixWord ++ tailWord_2726759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726759).length < 2 ^ (prefixWord ++ tailWord_2726759).sum := by decide
  have hdescent : baseEnd_2726759 < baseStart_2726759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726774 : List Nat := [5, 1, 1, 3, 1, 11]
def baseStart_2726774 : Nat := 118140960795 + 2726774 * 2 ^ 59
def prefixEnd_2726774 : Nat := 4983230072969 + 3 ^ 40 * 2726774 * 2
def baseEnd_2726774 : Nat := 11523832906856129365307

theorem tailTrace_2726774 : CollatzResearch.WordTrace tailWord_2726774 prefixEnd_2726774 11523832906856129365307 := by
  unfold tailWord_2726774
  simp only [CollatzResearch.WordTrace]
  refine ⟨6215851138960685548022711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66302412148913979178908917 6215851138960685548022711)
  ·
    refine ⟨9323776708441028322034067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6215851138960685548022711 9323776708441028322034067)
    ·
      refine ⟨13985665062661542483051101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9323776708441028322034067 13985665062661542483051101)
      ·
        refine ⟨5244624398498078431144163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13985665062661542483051101 5244624398498078431144163)
        ·
          refine ⟨7866936597747117646716245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5244624398498078431144163 7866936597747117646716245)
          ·
            refine ⟨11523832906856129365307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7866936597747117646716245 11523832906856129365307)
            ·
              rfl

theorem cell22_2726774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 11].length) (baseStart_2726774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726774 prefixEnd_2726774 := by exact prefixLift 2726774
  have htrace : WordTrace (prefixWord ++ tailWord_2726774) baseStart_2726774 baseEnd_2726774 := by
    simpa [prefixWord, tailWord_2726774, baseEnd_2726774] using wordTrace_append hprefix tailTrace_2726774
  have hstable : (prefixWord ++ tailWord_2726774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726774).length < 2 ^ (prefixWord ++ tailWord_2726774).sum := by decide
  have hdescent : baseEnd_2726774 < baseStart_2726774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726787 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 1, 8]
def baseStart_2726787 : Nat := 118140960795 + 2726787 * 2 ^ 59
def prefixEnd_2726787 : Nat := 4983230072969 + 3 ^ 40 * 2726787 * 2
def baseEnd_2726787 : Nat := 933434915621018778014827

theorem tailTrace_2726787 : CollatzResearch.WordTrace tailWord_2726787 prefixEnd_2726787 933434915621018778014827 := by
  unfold tailWord_2726787
  simp only [CollatzResearch.WordTrace]
  refine ⟨99454092372323871988586615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66302728248215914659057743 99454092372323871988586615)
  ·
    refine ⟨149181138558485807982879923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99454092372323871988586615 149181138558485807982879923)
    ·
      refine ⟨223771707837728711974319885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149181138558485807982879923 223771707837728711974319885)
      ·
        refine ⟨83914390439148266990369957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223771707837728711974319885 83914390439148266990369957)
        ·
          refine ⟨15733948207340300060694367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83914390439148266990369957 15733948207340300060694367)
          ·
            refine ⟨23600922311010450091041551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15733948207340300060694367 23600922311010450091041551)
            ·
              refine ⟨35401383466515675136562327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23600922311010450091041551 35401383466515675136562327)
              ·
                refine ⟨53102075199773512704843491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35401383466515675136562327 53102075199773512704843491)
                ·
                  refine ⟨79653112799660269057265237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53102075199773512704843491 79653112799660269057265237)
                  ·
                    refine ⟨933434915621018778014827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 79653112799660269057265237 933434915621018778014827)
                    ·
                      rfl

theorem cell22_2726787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 8].length) (baseStart_2726787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726787 prefixEnd_2726787 := by exact prefixLift 2726787
  have htrace : WordTrace (prefixWord ++ tailWord_2726787) baseStart_2726787 baseEnd_2726787 := by
    simpa [prefixWord, tailWord_2726787, baseEnd_2726787] using wordTrace_append hprefix tailTrace_2726787
  have hstable : (prefixWord ++ tailWord_2726787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726787).length < 2 ^ (prefixWord ++ tailWord_2726787).sum := by decide
  have hdescent : baseEnd_2726787 < baseStart_2726787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726804 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 2, 6]
def baseStart_2726804 : Nat := 118140960795 + 2726804 * 2 ^ 59
def prefixEnd_2726804 : Nat := 4983230072969 + 3 ^ 40 * 2726804 * 2
def baseEnd_2726804 : Nat := 933440735068436400339775

theorem tailTrace_2726804 : CollatzResearch.WordTrace tailWord_2726804 prefixEnd_2726804 933440735068436400339775 := by
  unfold tailWord_2726804
  simp only [CollatzResearch.WordTrace]
  refine ⟨49727356206631141945977733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66303141608841522594636977 49727356206631141945977733)
  ·
    refine ⟨9323879288743339114870825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49727356206631141945977733 9323879288743339114870825)
    ·
      refine ⟨6992909466557504336153119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9323879288743339114870825 6992909466557504336153119)
      ·
        refine ⟨10489364199836256504229679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6992909466557504336153119 10489364199836256504229679)
        ·
          refine ⟨15734046299754384756344519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10489364199836256504229679 15734046299754384756344519)
          ·
            refine ⟨23601069449631577134516779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15734046299754384756344519 23601069449631577134516779)
            ·
              refine ⟨35401604174447365701775169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23601069449631577134516779 35401604174447365701775169)
              ·
                refine ⟨26551203130835524276331377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35401604174447365701775169 26551203130835524276331377)
                ·
                  refine ⟨19913402348126643207248533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26551203130835524276331377 19913402348126643207248533)
                  ·
                    refine ⟨933440735068436400339775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19913402348126643207248533 933440735068436400339775)
                    ·
                      rfl

theorem cell22_2726804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_2726804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726804 prefixEnd_2726804 := by exact prefixLift 2726804
  have htrace : WordTrace (prefixWord ++ tailWord_2726804) baseStart_2726804 baseEnd_2726804 := by
    simpa [prefixWord, tailWord_2726804, baseEnd_2726804] using wordTrace_append hprefix tailTrace_2726804
  have hstable : (prefixWord ++ tailWord_2726804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726804).length < 2 ^ (prefixWord ++ tailWord_2726804).sum := by decide
  have hdescent : baseEnd_2726804 < baseStart_2726804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726896 : List Nat := [2, 1, 1, 1, 3, 2, 1, 6, 2, 3]
def baseStart_2726896 : Nat := 118140960795 + 2726896 * 2 ^ 59
def prefixEnd_2726896 : Nat := 4983230072969 + 3 ^ 40 * 2726896 * 2
def baseEnd_2726896 : Nat := 933472228548578827039493

theorem tailTrace_2726896 : CollatzResearch.WordTrace tailWord_2726896 prefixEnd_2726896 933472228548578827039493 := by
  unfold tailWord_2726896
  simp only [CollatzResearch.WordTrace]
  refine ⟨49729033964464491802152271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66305378619285989069536361 49729033964464491802152271)
  ·
    refine ⟨74593550946696737703228407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49729033964464491802152271 74593550946696737703228407)
    ·
      refine ⟨111890326420045106554842611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74593550946696737703228407 111890326420045106554842611)
      ·
        refine ⟨167835489630067659832263917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111890326420045106554842611 167835489630067659832263917)
        ·
          refine ⟨62938308611275372437098969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167835489630067659832263917 62938308611275372437098969)
          ·
            refine ⟨47203731458456529327824227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62938308611275372437098969 47203731458456529327824227)
            ·
              refine ⟨70805597187684793991736341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47203731458456529327824227 70805597187684793991736341)
              ·
                refine ⟨3319012368172724718362641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70805597187684793991736341 3319012368172724718362641)
                ·
                  refine ⟨2489259276129543538771981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3319012368172724718362641 2489259276129543538771981)
                  ·
                    refine ⟨933472228548578827039493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2489259276129543538771981 933472228548578827039493)
                    ·
                      rfl

theorem cell22_2726896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 2, 3].length) (baseStart_2726896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726896 prefixEnd_2726896 := by exact prefixLift 2726896
  have htrace : WordTrace (prefixWord ++ tailWord_2726896) baseStart_2726896 baseEnd_2726896 := by
    simpa [prefixWord, tailWord_2726896, baseEnd_2726896] using wordTrace_append hprefix tailTrace_2726896
  have hstable : (prefixWord ++ tailWord_2726896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726896).length < 2 ^ (prefixWord ++ tailWord_2726896).sum := by decide
  have hdescent : baseEnd_2726896 < baseStart_2726896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726913 : List Nat := [1, 2, 4, 1, 2, 3, 1, 3, 2, 3]
def baseStart_2726913 : Nat := 118140960795 + 2726913 * 2 ^ 59
def prefixEnd_2726913 : Nat := 4983230072969 + 3 ^ 40 * 2726913 * 2
def baseEnd_2726913 : Nat := 933478047995996449364441

theorem tailTrace_2726913 : CollatzResearch.WordTrace tailWord_2726913 prefixEnd_2726913 933478047995996449364441 := by
  unfold tailWord_2726913
  simp only [CollatzResearch.WordTrace]
  refine ⟨99458687969867395507673393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66305791979911597005115595 99458687969867395507673393)
  ·
    refine ⟨74594015977400546630755045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99458687969867395507673393 74594015977400546630755045)
    ·
      refine ⟨13986377995762602493266571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74594015977400546630755045 13986377995762602493266571)
      ·
        refine ⟨20979566993643903739899857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13986377995762602493266571 20979566993643903739899857)
        ·
          refine ⟨15734675245232927804924893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20979566993643903739899857 15734675245232927804924893)
          ·
            refine ⟨5900503216962347926846835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15734675245232927804924893 5900503216962347926846835)
            ·
              refine ⟨8850754825443521890270253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5900503216962347926846835 8850754825443521890270253)
              ·
                refine ⟨3319033059541320708851345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8850754825443521890270253 3319033059541320708851345)
                ·
                  refine ⟨2489274794655990531638509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3319033059541320708851345 2489274794655990531638509)
                  ·
                    refine ⟨933478047995996449364441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2489274794655990531638509 933478047995996449364441)
                    ·
                      rfl

theorem cell22_2726913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_2726913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726913 prefixEnd_2726913 := by exact prefixLift 2726913
  have htrace : WordTrace (prefixWord ++ tailWord_2726913) baseStart_2726913 baseEnd_2726913 := by
    simpa [prefixWord, tailWord_2726913, baseEnd_2726913] using wordTrace_append hprefix tailTrace_2726913
  have hstable : (prefixWord ++ tailWord_2726913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726913).length < 2 ^ (prefixWord ++ tailWord_2726913).sum := by decide
  have hdescent : baseEnd_2726913 < baseStart_2726913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726958 : List Nat := [4, 1, 3, 1, 1, 1, 2, 3, 3, 3]
def baseStart_2726958 : Nat := 118140960795 + 2726958 * 2 ^ 59
def prefixEnd_2726958 : Nat := 4983230072969 + 3 ^ 40 * 2726958 * 2
def baseEnd_2726958 : Nat := 933493452415631331989303

theorem tailTrace_2726958 : CollatzResearch.WordTrace tailWord_2726958 prefixEnd_2726958 933493452415631331989303 := by
  unfold tailWord_2726958
  simp only [CollatzResearch.WordTrace]
  refine ⟨12432541156838046024132691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66306886169802912128707685 12432541156838046024132691)
  ·
    refine ⟨18648811735257069036199037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12432541156838046024132691 18648811735257069036199037)
    ·
      refine ⟨6993304400721400888574639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18648811735257069036199037 6993304400721400888574639)
      ·
        refine ⟨10489956601082101332861959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6993304400721400888574639 10489956601082101332861959)
        ·
          refine ⟨15734934901623151999292939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10489956601082101332861959 15734934901623151999292939)
          ·
            refine ⟨23602402352434727998939409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15734934901623151999292939 23602402352434727998939409)
            ·
              refine ⟨17701801764326045999204557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23602402352434727998939409 17701801764326045999204557)
              ·
                refine ⟨6638175661622267249701709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17701801764326045999204557 6638175661622267249701709)
                ·
                  refine ⟨2489315873108350218638141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6638175661622267249701709 2489315873108350218638141)
                  ·
                    refine ⟨933493452415631331989303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2489315873108350218638141 933493452415631331989303)
                    ·
                      rfl

theorem cell22_2726958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_2726958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726958 prefixEnd_2726958 := by exact prefixLift 2726958
  have htrace : WordTrace (prefixWord ++ tailWord_2726958) baseStart_2726958 baseEnd_2726958 := by
    simpa [prefixWord, tailWord_2726958, baseEnd_2726958] using wordTrace_append hprefix tailTrace_2726958
  have hstable : (prefixWord ++ tailWord_2726958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726958).length < 2 ^ (prefixWord ++ tailWord_2726958).sum := by decide
  have hdescent : baseEnd_2726958 < baseStart_2726958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726999 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 10]
def baseStart_2726999 : Nat := 118140960795 + 2726999 * 2 ^ 59
def prefixEnd_2726999 : Nat := 4983230072969 + 3 ^ 40 * 2726999 * 2
def baseEnd_2726999 : Nat := 311169162517840297238059

theorem tailTrace_2726999 : CollatzResearch.WordTrace tailWord_2726999 prefixEnd_2726999 311169162517840297238059 := by
  unfold tailWord_2726999
  simp only [CollatzResearch.WordTrace]
  refine ⟨99461824647555832195304051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66307883098370554796869367 99461824647555832195304051)
  ·
    refine ⟨149192736971333748292956077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99461824647555832195304051 149192736971333748292956077)
    ·
      refine ⟨55947276364250155609858529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149192736971333748292956077 55947276364250155609858529)
      ·
        refine ⟨41960457273187616707393897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55947276364250155609858529 41960457273187616707393897)
        ·
          refine ⟨31470342954890712530545423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41960457273187616707393897 31470342954890712530545423)
          ·
            refine ⟨47205514432336068795818135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31470342954890712530545423 47205514432336068795818135)
            ·
              refine ⟨70808271648504103193727203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47205514432336068795818135 70808271648504103193727203)
              ·
                refine ⟨106212407472756154790590805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70808271648504103193727203 106212407472756154790590805)
                ·
                  refine ⟨311169162517840297238059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 106212407472756154790590805 311169162517840297238059)
                  ·
                    rfl

theorem cell22_2726999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 10].length) (baseStart_2726999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2726999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2726999 prefixEnd_2726999 := by exact prefixLift 2726999
  have htrace : WordTrace (prefixWord ++ tailWord_2726999) baseStart_2726999 baseEnd_2726999 := by
    simpa [prefixWord, tailWord_2726999, baseEnd_2726999] using wordTrace_append hprefix tailTrace_2726999
  have hstable : (prefixWord ++ tailWord_2726999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726999).length < 2 ^ (prefixWord ++ tailWord_2726999).sum := by decide
  have hdescent : baseEnd_2726999 < baseStart_2726999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727063 : List Nat := [1, 1, 3, 3, 3, 2, 1, 2, 2, 4]
def baseStart_2727063 : Nat := 118140960795 + 2727063 * 2 ^ 59
def prefixEnd_2727063 : Nat := 4983230072969 + 3 ^ 40 * 2727063 * 2
def baseEnd_2727063 : Nat := 933529396061446058113981

theorem tailTrace_2727063 : CollatzResearch.WordTrace tailWord_2727063 prefixEnd_2727063 933529396061446058113981 := by
  unfold tailWord_2727063
  simp only [CollatzResearch.WordTrace]
  refine ⟨99464158919323971125633843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66309439279549314083755895 99464158919323971125633843)
  ·
    refine ⟨149196238378985956688450765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99464158919323971125633843 149196238378985956688450765)
    ·
      refine ⟨55948589392119733758169037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149196238378985956688450765 55948589392119733758169037)
      ·
        refine ⟨20980721022044900159313389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55948589392119733758169037 20980721022044900159313389)
        ·
          refine ⟨7867770383266837559742521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20980721022044900159313389 7867770383266837559742521)
          ·
            refine ⟨5900827787450128169806891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7867770383266837559742521 5900827787450128169806891)
            ·
              refine ⟨8851241681175192254710337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5900827787450128169806891 8851241681175192254710337)
              ·
                refine ⟨6638431260881394191032753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8851241681175192254710337 6638431260881394191032753)
                ·
                  refine ⟨4978823445661045643274565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6638431260881394191032753 4978823445661045643274565)
                  ·
                    refine ⟨933529396061446058113981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4978823445661045643274565 933529396061446058113981)
                    ·
                      rfl

theorem cell22_2727063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_2727063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2727063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2727063 prefixEnd_2727063 := by exact prefixLift 2727063
  have htrace : WordTrace (prefixWord ++ tailWord_2727063) baseStart_2727063 baseEnd_2727063 := by
    simpa [prefixWord, tailWord_2727063, baseEnd_2727063] using wordTrace_append hprefix tailTrace_2727063
  have hstable : (prefixWord ++ tailWord_2727063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727063).length < 2 ^ (prefixWord ++ tailWord_2727063).sum := by decide
  have hdescent : baseEnd_2727063 < baseStart_2727063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727082 : List Nat := [3, 1, 5, 1, 1, 2, 1, 3, 2, 3]
def baseStart_2727082 : Nat := 118140960795 + 2727082 * 2 ^ 59
def prefixEnd_2727082 : Nat := 4983230072969 + 3 ^ 40 * 2727082 * 2
def baseEnd_2727082 : Nat := 933535900149736341888923

theorem tailTrace_2727082 : CollatzResearch.WordTrace tailWord_2727082 prefixEnd_2727082 933535900149736341888923 := by
  unfold tailWord_2727082
  simp only [CollatzResearch.WordTrace]
  refine ⟨24866212976563784342643875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66309901270836758247050333 24866212976563784342643875)
  ·
    refine ⟨37299319464845676513965813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24866212976563784342643875 37299319464845676513965813)
    ·
      refine ⟨3496811199829282173184295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37299319464845676513965813 3496811199829282173184295)
      ·
        refine ⟨5245216799743923259776443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3496811199829282173184295 5245216799743923259776443)
        ·
          refine ⟨7867825199615884889664665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5245216799743923259776443 7867825199615884889664665)
          ·
            refine ⟨5900868899711913667248499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7867825199615884889664665 5900868899711913667248499)
            ·
              refine ⟨8851303349567870500872749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5900868899711913667248499 8851303349567870500872749)
              ·
                refine ⟨3319238756087951437827281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8851303349567870500872749 3319238756087951437827281)
                ·
                  refine ⟨2489429067065963578370461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3319238756087951437827281 2489429067065963578370461)
                  ·
                    refine ⟨933535900149736341888923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2489429067065963578370461 933535900149736341888923)
                    ·
                      rfl

theorem cell22_2727082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_2727082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2727082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2727082 prefixEnd_2727082 := by exact prefixLift 2727082
  have htrace : WordTrace (prefixWord ++ tailWord_2727082) baseStart_2727082 baseEnd_2727082 := by
    simpa [prefixWord, tailWord_2727082, baseEnd_2727082] using wordTrace_append hprefix tailTrace_2727082
  have hstable : (prefixWord ++ tailWord_2727082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727082).length < 2 ^ (prefixWord ++ tailWord_2727082).sum := by decide
  have hdescent : baseEnd_2727082 < baseStart_2727082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727121 : List Nat := [1, 2, 2, 1, 2, 2, 1, 4, 2, 5]
def baseStart_2727121 : Nat := 118140960795 + 2727121 * 2 ^ 59
def prefixEnd_2727121 : Nat := 4983230072969 + 3 ^ 40 * 2727121 * 2
def baseEnd_2727121 : Nat := 933549250646753240163803

theorem tailTrace_2727121 : CollatzResearch.WordTrace tailWord_2727121 prefixEnd_2727121 933549250646753240163803 := by
  unfold tailWord_2727121
  simp only [CollatzResearch.WordTrace]
  refine ⟨99466274353113847031245217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66310849568742564687496811 99466274353113847031245217)
  ·
    refine ⟨74599705764835385273433913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99466274353113847031245217 74599705764835385273433913)
    ·
      refine ⟨55949779323626538955075435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74599705764835385273433913 55949779323626538955075435)
      ·
        refine ⟨83924668985439808432613153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55949779323626538955075435 83924668985439808432613153)
        ·
          refine ⟨62943501739079856324459865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83924668985439808432613153 62943501739079856324459865)
          ·
            refine ⟨47207626304309892243344899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62943501739079856324459865 47207626304309892243344899)
            ·
              refine ⟨70811439456464838365017349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47207626304309892243344899 70811439456464838365017349)
              ·
                refine ⟨13277144898087157193440753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70811439456464838365017349 13277144898087157193440753)
                ·
                  refine ⟨9957858673565367895080565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13277144898087157193440753 9957858673565367895080565)
                  ·
                    refine ⟨933549250646753240163803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9957858673565367895080565 933549250646753240163803)
                    ·
                      rfl

theorem cell22_2727121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_2727121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2727121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2727121 prefixEnd_2727121 := by exact prefixLift 2727121
  have htrace : WordTrace (prefixWord ++ tailWord_2727121) baseStart_2727121 baseEnd_2727121 := by
    simpa [prefixWord, tailWord_2727121, baseEnd_2727121] using wordTrace_append hprefix tailTrace_2727121
  have hstable : (prefixWord ++ tailWord_2727121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727121).length < 2 ^ (prefixWord ++ tailWord_2727121).sum := by decide
  have hdescent : baseEnd_2727121 < baseStart_2727121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727127 : List Nat := [1, 1, 3, 2, 1, 2, 6, 2, 1, 3]
def baseStart_2727127 : Nat := 118140960795 + 2727127 * 2 ^ 59
def prefixEnd_2727127 : Nat := 4983230072969 + 3 ^ 40 * 2727127 * 2
def baseEnd_2727127 : Nat := 933551304569371224513785

theorem tailTrace_2727127 : CollatzResearch.WordTrace tailWord_2727127 prefixEnd_2727127 933551304569371224513785 := by
  unfold tailWord_2727127
  simp only [CollatzResearch.WordTrace]
  refine ⟨99466493191092110055963635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66310995460728073370642423 99466493191092110055963635)
  ·
    refine ⟨149199739786638165083945453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99466493191092110055963635 149199739786638165083945453)
    ·
      refine ⟨55949902419989311906479545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149199739786638165083945453 55949902419989311906479545)
      ·
        refine ⟨41962426814991983929859659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55949902419989311906479545 41962426814991983929859659)
        ·
          refine ⟨62943640222487975894789489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41962426814991983929859659 62943640222487975894789489)
          ·
            refine ⟨47207730166865981921092117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62943640222487975894789489 47207730166865981921092117)
            ·
              refine ⟨2212862351571842902551193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47207730166865981921092117 2212862351571842902551193)
              ·
                refine ⟨1659646763678882176913395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2212862351571842902551193 1659646763678882176913395)
                ·
                  refine ⟨2489470145518323265370093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1659646763678882176913395 2489470145518323265370093)
                  ·
                    refine ⟨933551304569371224513785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2489470145518323265370093 933551304569371224513785)
                    ·
                      rfl

theorem cell22_2727127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 2, 1, 3].length) (baseStart_2727127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2727127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2727127 prefixEnd_2727127 := by exact prefixLift 2727127
  have htrace : WordTrace (prefixWord ++ tailWord_2727127) baseStart_2727127 baseEnd_2727127 := by
    simpa [prefixWord, tailWord_2727127, baseEnd_2727127] using wordTrace_append hprefix tailTrace_2727127
  have hstable : (prefixWord ++ tailWord_2727127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727127).length < 2 ^ (prefixWord ++ tailWord_2727127).sum := by decide
  have hdescent : baseEnd_2727127 < baseStart_2727127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727153 : List Nat := [1, 2, 2, 2, 2, 1, 1, 6, 1, 4]
def baseStart_2727153 : Nat := 118140960795 + 2727153 * 2 ^ 59
def prefixEnd_2727153 : Nat := 4983230072969 + 3 ^ 40 * 2727153 * 2
def baseEnd_2727153 : Nat := 933560204900715823363705

theorem tailTrace_2727153 : CollatzResearch.WordTrace tailWord_2727153 prefixEnd_2727153 933560204900715823363705 := by
  unfold tailWord_2727153
  simp only [CollatzResearch.WordTrace]
  refine ⟨99467441488997916496410113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66311627659331944330940075 99467441488997916496410113)
  ·
    refine ⟨74600581116748437372307585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99467441488997916496410113 74600581116748437372307585)
    ·
      refine ⟨55950435837561328029230689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74600581116748437372307585 55950435837561328029230689)
      ·
        refine ⟨41962826878170996021923017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55950435837561328029230689 41962826878170996021923017)
        ·
          refine ⟨31472120158628247016442263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41962826878170996021923017 31472120158628247016442263)
          ·
            refine ⟨47208180237942370524663395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31472120158628247016442263 47208180237942370524663395)
            ·
              refine ⟨70812270356913555786995093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47208180237942370524663395 70812270356913555786995093)
              ·
                refine ⟨3319325172980322927515395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70812270356913555786995093 3319325172980322927515395)
                ·
                  refine ⟨4978987759470484391273093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3319325172980322927515395 4978987759470484391273093)
                  ·
                    refine ⟨933560204900715823363705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4978987759470484391273093 933560204900715823363705)
                    ·
                      rfl

theorem cell22_2727153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_2727153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2727153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2727153 prefixEnd_2727153 := by exact prefixLift 2727153
  have htrace : WordTrace (prefixWord ++ tailWord_2727153) baseStart_2727153 baseEnd_2727153 := by
    simpa [prefixWord, tailWord_2727153, baseEnd_2727153] using wordTrace_append hprefix tailTrace_2727153
  have hstable : (prefixWord ++ tailWord_2727153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727153).length < 2 ^ (prefixWord ++ tailWord_2727153).sum := by decide
  have hdescent : baseEnd_2727153 < baseStart_2727153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727335 : List Nat := [1, 1, 6, 1, 1, 1, 1, 4, 1, 5]
def baseStart_2727335 : Nat := 118140960795 + 2727335 * 2 ^ 59
def prefixEnd_2727335 : Nat := 4983230072969 + 3 ^ 40 * 2727335 * 2
def baseEnd_2727335 : Nat := 933622507220128015313147

theorem tailTrace_2727335 : CollatzResearch.WordTrace tailWord_2727335 prefixEnd_2727335 933622507220128015313147 := by
  unfold tailWord_2727335
  simp only [CollatzResearch.WordTrace]
  refine ⟨99474079574338561579535459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66316053049559041053023639 99474079574338561579535459)
  ·
    refine ⟨149211119361507842369303189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99474079574338561579535459 149211119361507842369303189)
    ·
      refine ⟨6994271220070680111061087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 149211119361507842369303189 6994271220070680111061087)
      ·
        refine ⟨10491406830106020166591631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6994271220070680111061087 10491406830106020166591631)
        ·
          refine ⟨15737110245159030249887447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10491406830106020166591631 15737110245159030249887447)
          ·
            refine ⟨23605665367738545374831171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15737110245159030249887447 23605665367738545374831171)
            ·
              refine ⟨35408498051607818062246757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23605665367738545374831171 35408498051607818062246757)
              ·
                refine ⟨6639093384676465886671267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35408498051607818062246757 6639093384676465886671267)
                ·
                  refine ⟨9958640077014698830006901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6639093384676465886671267 9958640077014698830006901)
                  ·
                    refine ⟨933622507220128015313147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9958640077014698830006901 933622507220128015313147)
                    ·
                      rfl

theorem cell22_2727335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_2727335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2727335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2727335 prefixEnd_2727335 := by exact prefixLift 2727335
  have htrace : WordTrace (prefixWord ++ tailWord_2727335) baseStart_2727335 baseEnd_2727335 := by
    simpa [prefixWord, tailWord_2727335, baseEnd_2727335] using wordTrace_append hprefix tailTrace_2727335
  have hstable : (prefixWord ++ tailWord_2727335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727335).length < 2 ^ (prefixWord ++ tailWord_2727335).sum := by decide
  have hdescent : baseEnd_2727335 < baseStart_2727335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727352 : List Nat := [2, 1, 2, 1, 2, 2, 5, 2, 2, 3]
def baseStart_2727352 : Nat := 118140960795 + 2727352 * 2 ^ 59
def prefixEnd_2727352 : Nat := 4983230072969 + 3 ^ 40 * 2727352 * 2
def baseEnd_2727352 : Nat := 933628326667545637638095

theorem tailTrace_2727352 : CollatzResearch.WordTrace tailWord_2727352 prefixEnd_2727352 933628326667545637638095 := by
  unfold tailWord_2727352
  simp only [CollatzResearch.WordTrace]
  refine ⟨49737349807638486741452155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66316466410184648988602873 49737349807638486741452155)
  ·
    refine ⟨74606024711457730112178233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49737349807638486741452155 74606024711457730112178233)
    ·
      refine ⟨55954518533593297584133675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74606024711457730112178233 55954518533593297584133675)
      ·
        refine ⟨83931777800389946376200513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55954518533593297584133675 83931777800389946376200513)
        ·
          refine ⟨62948833350292459782150385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83931777800389946376200513 62948833350292459782150385)
          ·
            refine ⟨47211625012719344836612789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62948833350292459782150385 47211625012719344836612789)
            ·
              refine ⟨4426089844942438578432449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47211625012719344836612789 4426089844942438578432449)
              ·
                refine ⟨3319567383706828933824337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4426089844942438578432449 3319567383706828933824337)
                ·
                  refine ⟨2489675537780121700368253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3319567383706828933824337 2489675537780121700368253)
                  ·
                    refine ⟨933628326667545637638095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2489675537780121700368253 933628326667545637638095)
                    ·
                      rfl

theorem cell22_2727352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 2, 3].length) (baseStart_2727352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2727352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2727352 prefixEnd_2727352 := by exact prefixLift 2727352
  have htrace : WordTrace (prefixWord ++ tailWord_2727352) baseStart_2727352 baseEnd_2727352 := by
    simpa [prefixWord, tailWord_2727352, baseEnd_2727352] using wordTrace_append hprefix tailTrace_2727352
  have hstable : (prefixWord ++ tailWord_2727352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727352).length < 2 ^ (prefixWord ++ tailWord_2727352).sum := by decide
  have hdescent : baseEnd_2727352 < baseStart_2727352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727382 : List Nat := [5, 2, 1, 1, 1, 3, 1, 8]
def baseStart_2727382 : Nat := 118140960795 + 2727382 * 2 ^ 59
def prefixEnd_2727382 : Nat := 4983230072969 + 3 ^ 40 * 2727382 * 2
def baseEnd_2727382 : Nat := 103737621808959506598667

theorem tailTrace_2727382 : CollatzResearch.WordTrace tailWord_2727382 prefixEnd_2727382 103737621808959506598667 := by
  unfold tailWord_2727382
  simp only [CollatzResearch.WordTrace]
  refine ⟨6217237112823018037906025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66317195870112192404330933 6217237112823018037906025)
  ·
    refine ⟨4662927834617263528429519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6217237112823018037906025 4662927834617263528429519)
    ·
      refine ⟨6994391751925895292644279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4662927834617263528429519 6994391751925895292644279)
      ·
        refine ⟨10491587627888842938966419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6994391751925895292644279 10491587627888842938966419)
        ·
          refine ⟨15737381441833264408449629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10491587627888842938966419 15737381441833264408449629)
          ·
            refine ⟨5901518040687474153168611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15737381441833264408449629 5901518040687474153168611)
            ·
              refine ⟨8852277061031211229752917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5901518040687474153168611 8852277061031211229752917)
              ·
                refine ⟨103737621808959506598667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8852277061031211229752917 103737621808959506598667)
                ·
                  rfl

theorem cell22_2727382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_2727382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2727382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2727382 prefixEnd_2727382 := by exact prefixLift 2727382
  have htrace : WordTrace (prefixWord ++ tailWord_2727382) baseStart_2727382 baseEnd_2727382 := by
    simpa [prefixWord, tailWord_2727382, baseEnd_2727382] using wordTrace_append hprefix tailTrace_2727382
  have hstable : (prefixWord ++ tailWord_2727382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727382).length < 2 ^ (prefixWord ++ tailWord_2727382).sum := by decide
  have hdescent : baseEnd_2727382 < baseStart_2727382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727414 : List Nat := [5, 1, 1, 1, 2, 2, 3, 1, 3, 3]
def baseStart_2727414 : Nat := 118140960795 + 2727414 * 2 ^ 59
def prefixEnd_2727414 : Nat := 4983230072969 + 3 ^ 40 * 2727414 * 2
def baseEnd_2727414 : Nat := 933649550534598142587905

theorem tailTrace_2727414 : CollatzResearch.WordTrace tailWord_2727414 prefixEnd_2727414 933649550534598142587905 := by
  unfold tailWord_2727414
  simp only [CollatzResearch.WordTrace]
  refine ⟨6217310058815772379478831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66317973960701572047774197 6217310058815772379478831)
  ·
    refine ⟨9325965088223658569218247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6217310058815772379478831 9325965088223658569218247)
    ·
      refine ⟨13988947632335487853827371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9325965088223658569218247 13988947632335487853827371)
      ·
        refine ⟨20983421448503231780741057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13988947632335487853827371 20983421448503231780741057)
        ·
          refine ⟨15737566086377423835555793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20983421448503231780741057 15737566086377423835555793)
          ·
            refine ⟨11803174564783067876666845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15737566086377423835555793 11803174564783067876666845)
            ·
              refine ⟨4426190461793650453750067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11803174564783067876666845 4426190461793650453750067)
              ·
                refine ⟨6639285692690475680625101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4426190461793650453750067 6639285692690475680625101)
                ·
                  refine ⟨2489732134758928380234413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6639285692690475680625101 2489732134758928380234413)
                  ·
                    refine ⟨933649550534598142587905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2489732134758928380234413 933649550534598142587905)
                    ·
                      rfl

theorem cell22_2727414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_2727414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2727414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2727414 prefixEnd_2727414 := by exact prefixLift 2727414
  have htrace : WordTrace (prefixWord ++ tailWord_2727414) baseStart_2727414 baseEnd_2727414 := by
    simpa [prefixWord, tailWord_2727414, baseEnd_2727414] using wordTrace_append hprefix tailTrace_2727414
  have hstable : (prefixWord ++ tailWord_2727414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727414).length < 2 ^ (prefixWord ++ tailWord_2727414).sum := by decide
  have hdescent : baseEnd_2727414 < baseStart_2727414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727487 : List Nat := [1, 1, 2, 2, 3, 4, 2, 1, 1, 5]
def baseStart_2727487 : Nat := 118140960795 + 2727487 * 2 ^ 59
def prefixEnd_2727487 : Nat := 4983230072969 + 3 ^ 40 * 2727487 * 2
def baseEnd_2727487 : Nat := 933674539926450285512681

theorem tailTrace_2727487 : CollatzResearch.WordTrace tailWord_2727487 prefixEnd_2727487 933674539926450285512681 := by
  unfold tailWord_2727487
  simp only [CollatzResearch.WordTrace]
  refine ⟨99479623469787891539068715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66319748979858594359379143 99479623469787891539068715)
  ·
    refine ⟨149219435204681837308603073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99479623469787891539068715 149219435204681837308603073)
    ·
      refine ⟨111914576403511377981452305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149219435204681837308603073 111914576403511377981452305)
      ·
        refine ⟨83935932302633533486089229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111914576403511377981452305 83935932302633533486089229)
        ·
          refine ⟨31475974613487575057283461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83935932302633533486089229 31475974613487575057283461)
          ·
            refine ⟨5901745240028920323240649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31475974613487575057283461 5901745240028920323240649)
            ·
              refine ⟨4426308930021690242430487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5901745240028920323240649 4426308930021690242430487)
              ·
                refine ⟨6639463395032535363645731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4426308930021690242430487 6639463395032535363645731)
                ·
                  refine ⟨9959195092548803045468597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6639463395032535363645731 9959195092548803045468597)
                  ·
                    refine ⟨933674539926450285512681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9959195092548803045468597 933674539926450285512681)
                    ·
                      rfl

theorem cell22_2727487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 5].length) (baseStart_2727487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2727487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2727487 prefixEnd_2727487 := by exact prefixLift 2727487
  have htrace : WordTrace (prefixWord ++ tailWord_2727487) baseStart_2727487 baseEnd_2727487 := by
    simpa [prefixWord, tailWord_2727487, baseEnd_2727487] using wordTrace_append hprefix tailTrace_2727487
  have hstable : (prefixWord ++ tailWord_2727487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727487).length < 2 ^ (prefixWord ++ tailWord_2727487).sum := by decide
  have hdescent : baseEnd_2727487 < baseStart_2727487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727549 : List Nat := [1, 4, 1, 1, 4, 1, 2, 2, 3, 3]
def baseStart_2727549 : Nat := 118140960795 + 2727549 * 2 ^ 59
def prefixEnd_2727549 : Nat := 4983230072969 + 3 ^ 40 * 2727549 * 2
def baseEnd_2727549 : Nat := 933695763793502790462491

theorem tailTrace_2727549 : CollatzResearch.WordTrace tailWord_2727549 prefixEnd_2727549 933695763793502790462491 := by
  unfold tailWord_2727549
  simp only [CollatzResearch.WordTrace]
  refine ⟨99481884795563276127825701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66321256530375517418550467 99481884795563276127825701)
  ·
    refine ⟨18652853399168114273967319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99481884795563276127825701 18652853399168114273967319)
    ·
      refine ⟨27979280098752171410950979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18652853399168114273967319 27979280098752171410950979)
      ·
        refine ⟨41968920148128257116426469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27979280098752171410950979 41968920148128257116426469)
        ·
          refine ⟨7869172527774048209329963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41968920148128257116426469 7869172527774048209329963)
          ·
            refine ⟨11803758791661072313994945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7869172527774048209329963 11803758791661072313994945)
            ·
              refine ⟨8852819093745804235496209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11803758791661072313994945 8852819093745804235496209)
              ·
                refine ⟨6639614320309353176622157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8852819093745804235496209 6639614320309353176622157)
                ·
                  refine ⟨2489855370116007441233309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6639614320309353176622157 2489855370116007441233309)
                  ·
                    refine ⟨933695763793502790462491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2489855370116007441233309 933695763793502790462491)
                    ·
                      rfl

theorem cell22_2727549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_2727549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2727549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2727549 prefixEnd_2727549 := by exact prefixLift 2727549
  have htrace : WordTrace (prefixWord ++ tailWord_2727549) baseStart_2727549 baseEnd_2727549 := by
    simpa [prefixWord, tailWord_2727549, baseEnd_2727549] using wordTrace_append hprefix tailTrace_2727549
  have hstable : (prefixWord ++ tailWord_2727549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727549).length < 2 ^ (prefixWord ++ tailWord_2727549).sum := by decide
  have hdescent : baseEnd_2727549 < baseStart_2727549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727562 : List Nat := [3, 1, 2, 3, 2, 1, 1, 2, 7]
def baseStart_2727562 : Nat := 118140960795 + 2727562 * 2 ^ 59
def prefixEnd_2727562 : Nat := 4983230072969 + 3 ^ 40 * 2727562 * 2
def baseEnd_2727562 : Nat := 311233404653058363295817

theorem tailTrace_2727562 : CollatzResearch.WordTrace tailWord_2727562 prefixEnd_2727562 311233404653058363295817 := by
  unfold tailWord_2727562
  simp only [CollatzResearch.WordTrace]
  refine ⟨24870589736129044837012235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66321572629677452898699293 24870589736129044837012235)
  ·
    refine ⟨37305884604193567255518353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24870589736129044837012235 37305884604193567255518353)
    ·
      refine ⟨27979413453145175441638765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37305884604193567255518353 27979413453145175441638765)
      ·
        refine ⟨10492280044929440790614537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27979413453145175441638765 10492280044929440790614537)
        ·
          refine ⟨7869210033697080592960903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10492280044929440790614537 7869210033697080592960903)
          ·
            refine ⟨11803815050545620889441355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7869210033697080592960903 11803815050545620889441355)
            ·
              refine ⟨17705722575818431334162033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11803815050545620889441355 17705722575818431334162033)
              ·
                refine ⟨13279291931863823500621525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17705722575818431334162033 13279291931863823500621525)
                ·
                  refine ⟨311233404653058363295817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13279291931863823500621525 311233404653058363295817)
                  ·
                    rfl

theorem cell22_2727562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 7].length) (baseStart_2727562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2727562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2727562 prefixEnd_2727562 := by exact prefixLift 2727562
  have htrace : WordTrace (prefixWord ++ tailWord_2727562) baseStart_2727562 baseEnd_2727562 := by
    simpa [prefixWord, tailWord_2727562, baseEnd_2727562] using wordTrace_append hprefix tailTrace_2727562
  have hstable : (prefixWord ++ tailWord_2727562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727562).length < 2 ^ (prefixWord ++ tailWord_2727562).sum := by decide
  have hdescent : baseEnd_2727562 < baseStart_2727562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727583 : List Nat := [1, 1, 2, 7, 1, 2, 1, 1, 3, 3]
def baseStart_2727583 : Nat := 118140960795 + 2727583 * 2 ^ 59
def prefixEnd_2727583 : Nat := 4983230072969 + 3 ^ 40 * 2727583 * 2
def baseEnd_2727583 : Nat := 933707402688338035112387

theorem tailTrace_2727583 : CollatzResearch.WordTrace tailWord_2727583 prefixEnd_2727583 933707402688338035112387 := by
  unfold tailWord_2727583
  simp only [CollatzResearch.WordTrace]
  refine ⟨99483124877440099934563403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66322083251626733289708935 99483124877440099934563403)
  ·
    refine ⟨149224687316160149901845105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99483124877440099934563403 149224687316160149901845105)
    ·
      refine ⟨111918515487120112426383829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149224687316160149901845105 111918515487120112426383829)
      ·
        refine ⟨2623090206729377634993371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 111918515487120112426383829 2623090206729377634993371)
        ·
          refine ⟨3934635310094066452490057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2623090206729377634993371 3934635310094066452490057)
          ·
            refine ⟨2950976482570549839367543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3934635310094066452490057 2950976482570549839367543)
            ·
              refine ⟨4426464723855824759051315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2950976482570549839367543 4426464723855824759051315)
              ·
                refine ⟨6639697085783737138576973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4426464723855824759051315 6639697085783737138576973)
                ·
                  refine ⟨2489886407168901426966365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6639697085783737138576973 2489886407168901426966365)
                  ·
                    refine ⟨933707402688338035112387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2489886407168901426966365 933707402688338035112387)
                    ·
                      rfl

theorem cell22_2727583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 3, 3].length) (baseStart_2727583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2727583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2727583 prefixEnd_2727583 := by exact prefixLift 2727583
  have htrace : WordTrace (prefixWord ++ tailWord_2727583) baseStart_2727583 baseEnd_2727583 := by
    simpa [prefixWord, tailWord_2727583, baseEnd_2727583] using wordTrace_append hprefix tailTrace_2727583
  have hstable : (prefixWord ++ tailWord_2727583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727583).length < 2 ^ (prefixWord ++ tailWord_2727583).sum := by decide
  have hdescent : baseEnd_2727583 < baseStart_2727583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727609 : List Nat := [1, 2, 1, 4, 1, 1, 5, 2, 1, 4]
def baseStart_2727609 : Nat := 118140960795 + 2727609 * 2 ^ 59
def prefixEnd_2727609 : Nat := 4983230072969 + 3 ^ 40 * 2727609 * 2
def baseEnd_2727609 : Nat := 933716303019682633962307

theorem tailTrace_2727609 : CollatzResearch.WordTrace tailWord_2727609 prefixEnd_2727609 933716303019682633962307 := by
  unfold tailWord_2727609
  simp only [CollatzResearch.WordTrace]
  refine ⟨99484073175345906375009881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66322715450230604250006587 99484073175345906375009881)
  ·
    refine ⟨74613054881509429781257411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99484073175345906375009881 74613054881509429781257411)
    ·
      refine ⟨111919582322264144671886117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74613054881509429781257411 111919582322264144671886117)
      ·
        refine ⟨20984921685424527125978647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111919582322264144671886117 20984921685424527125978647)
        ·
          refine ⟨31477382528136790688967971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20984921685424527125978647 31477382528136790688967971)
          ·
            refine ⟨47216073792205186033451957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31477382528136790688967971 47216073792205186033451957)
            ·
              refine ⟨4426506918019236190636121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47216073792205186033451957 4426506918019236190636121)
              ·
                refine ⟨3319880188514427142977091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4426506918019236190636121 3319880188514427142977091)
                ·
                  refine ⟨4979820282771640714465637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3319880188514427142977091 4979820282771640714465637)
                  ·
                    refine ⟨933716303019682633962307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4979820282771640714465637 933716303019682633962307)
                    ·
                      rfl

theorem cell22_2727609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 4].length) (baseStart_2727609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2727609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2727609 prefixEnd_2727609 := by exact prefixLift 2727609
  have htrace : WordTrace (prefixWord ++ tailWord_2727609) baseStart_2727609 baseEnd_2727609 := by
    simpa [prefixWord, tailWord_2727609, baseEnd_2727609] using wordTrace_append hprefix tailTrace_2727609
  have hstable : (prefixWord ++ tailWord_2727609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727609).length < 2 ^ (prefixWord ++ tailWord_2727609).sum := by decide
  have hdescent : baseEnd_2727609 < baseStart_2727609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727624 : List Nat := [2, 1, 3, 1, 2, 2, 2, 5, 4]
def baseStart_2727624 : Nat := 118140960795 + 2727624 * 2 ^ 59
def prefixEnd_2727624 : Nat := 4983230072969 + 3 ^ 40 * 2727624 * 2
def baseEnd_2727624 : Nat := 311240479275409198279087

theorem tailTrace_2727624 : CollatzResearch.WordTrace tailWord_2727624 prefixEnd_2727624 311240479275409198279087 := by
  unfold tailWord_2727624
  simp only [CollatzResearch.WordTrace]
  refine ⟨49742310135145781968402963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66323080180194375957870617 49742310135145781968402963)
  ·
    refine ⟨74613465202718672952604445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49742310135145781968402963 74613465202718672952604445)
    ·
      refine ⟨27980049451019502357226667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74613465202718672952604445 27980049451019502357226667)
      ·
        refine ⟨41970074176529253535840001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27980049451019502357226667 41970074176529253535840001)
        ·
          refine ⟨31477555632396940151880001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41970074176529253535840001 31477555632396940151880001)
          ·
            refine ⟨23608166724297705113910001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31477555632396940151880001 23608166724297705113910001)
            ·
              refine ⟨17706125043223278835432501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23608166724297705113910001 17706125043223278835432501)
              ·
                refine ⟨1659949222802182390821797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17706125043223278835432501 1659949222802182390821797)
                ·
                  refine ⟨311240479275409198279087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1659949222802182390821797 311240479275409198279087)
                  ·
                    rfl

theorem cell22_2727624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 5, 4].length) (baseStart_2727624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2727624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2727624 prefixEnd_2727624 := by exact prefixLift 2727624
  have htrace : WordTrace (prefixWord ++ tailWord_2727624) baseStart_2727624 baseEnd_2727624 := by
    simpa [prefixWord, tailWord_2727624, baseEnd_2727624] using wordTrace_append hprefix tailTrace_2727624
  have hstable : (prefixWord ++ tailWord_2727624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727624).length < 2 ^ (prefixWord ++ tailWord_2727624).sum := by decide
  have hdescent : baseEnd_2727624 < baseStart_2727624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727641 : List Nat := [1, 2, 1, 2, 3, 3, 4, 2, 4]
def baseStart_2727641 : Nat := 118140960795 + 2727641 * 2 ^ 59
def prefixEnd_2727641 : Nat := 4983230072969 + 3 ^ 40 * 2727641 * 2
def baseEnd_2727641 : Nat := 311242419091215072387403

theorem tailTrace_2727641 : CollatzResearch.WordTrace tailWord_2727641 prefixEnd_2727641 311242419091215072387403 := by
  unfold tailWord_2727641
  simp only [CollatzResearch.WordTrace]
  refine ⟨99485240311229975840174777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66323493540819983893449851 99485240311229975840174777)
  ·
    refine ⟨74613930233422481880131083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99485240311229975840174777 74613930233422481880131083)
    ·
      refine ⟨111920895350133722820196625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74613930233422481880131083 111920895350133722820196625)
      ·
        refine ⟨83940671512600292115147469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111920895350133722820196625 83940671512600292115147469)
        ·
          refine ⟨31477751817225109543180301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83940671512600292115147469 31477751817225109543180301)
          ·
            refine ⟨11804156931459416078692613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31477751817225109543180301 11804156931459416078692613)
            ·
              refine ⟨2213279424648640514754865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11804156931459416078692613 2213279424648640514754865)
              ·
                refine ⟨1659959568486480386066149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2213279424648640514754865 1659959568486480386066149)
                ·
                  refine ⟨311242419091215072387403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1659959568486480386066149 311242419091215072387403)
                  ·
                    rfl

theorem cell22_2727641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 2, 4].length) (baseStart_2727641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2727641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2727641 prefixEnd_2727641 := by exact prefixLift 2727641
  have htrace : WordTrace (prefixWord ++ tailWord_2727641) baseStart_2727641 baseEnd_2727641 := by
    simpa [prefixWord, tailWord_2727641, baseEnd_2727641] using wordTrace_append hprefix tailTrace_2727641
  have hstable : (prefixWord ++ tailWord_2727641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727641).length < 2 ^ (prefixWord ++ tailWord_2727641).sum := by decide
  have hdescent : baseEnd_2727641 < baseStart_2727641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727656 : List Nat := [2, 1, 4, 1, 3, 1, 2, 3, 2, 3]
def baseStart_2727656 : Nat := 118140960795 + 2727656 * 2 ^ 59
def prefixEnd_2727656 : Nat := 4983230072969 + 3 ^ 40 * 2727656 * 2
def baseEnd_2727656 : Nat := 933732392080190178037163

theorem tailTrace_2727656 : CollatzResearch.WordTrace tailWord_2727656 prefixEnd_2727656 933732392080190178037163 := by
  unfold tailWord_2727656
  simp only [CollatzResearch.WordTrace]
  refine ⟨49742893703087816700985411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66323858270783755601313881 49742893703087816700985411)
  ·
    refine ⟨74614340554631725051478117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49742893703087816700985411 74614340554631725051478117)
    ·
      refine ⟨13990188853993448447152147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74614340554631725051478117 13990188853993448447152147)
      ·
        refine ⟨20985283280990172670728221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13990188853993448447152147 20985283280990172670728221)
        ·
          refine ⟨7869481230371314751523083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20985283280990172670728221 7869481230371314751523083)
          ·
            refine ⟨11804221845556972127284625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7869481230371314751523083 11804221845556972127284625)
            ·
              refine ⟨8853166384167729095463469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11804221845556972127284625 8853166384167729095463469)
              ·
                refine ⟨3319937394062898410798801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8853166384167729095463469 3319937394062898410798801)
                ·
                  refine ⟨2489953045547173808099101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3319937394062898410798801 2489953045547173808099101)
                  ·
                    refine ⟨933732392080190178037163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2489953045547173808099101 933732392080190178037163)
                    ·
                      rfl

theorem cell22_2727656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_2727656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2727656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2727656 prefixEnd_2727656 := by exact prefixLift 2727656
  have htrace : WordTrace (prefixWord ++ tailWord_2727656) baseStart_2727656 baseEnd_2727656 := by
    simpa [prefixWord, tailWord_2727656, baseEnd_2727656] using wordTrace_append hprefix tailTrace_2727656
  have hstable : (prefixWord ++ tailWord_2727656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727656).length < 2 ^ (prefixWord ++ tailWord_2727656).sum := by decide
  have hdescent : baseEnd_2727656 < baseStart_2727656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727701 : List Nat := [1, 3, 2, 1, 2, 4, 2, 1, 3, 3]
def baseStart_2727701 : Nat := 118140960795 + 2727701 * 2 ^ 59
def prefixEnd_2727701 : Nat := 4983230072969 + 3 ^ 40 * 2727701 * 2
def baseEnd_2727701 : Nat := 933747796499825060662025

theorem tailTrace_2727701 : CollatzResearch.WordTrace tailWord_2727701 prefixEnd_2727701 933747796499825060662025 := by
  unfold tailWord_2727701
  simp only [CollatzResearch.WordTrace]
  refine ⟨99487428691012606087358957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66324952460675070724905971 99487428691012606087358957)
  ·
    refine ⟨37307785759129727282759609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99487428691012606087358957 37307785759129727282759609)
    ·
      refine ⟨27980839319347295462069707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37307785759129727282759609 27980839319347295462069707)
      ·
        refine ⟨41971258979020943193104561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27980839319347295462069707 41971258979020943193104561)
        ·
          refine ⟨31478444234265707394828421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41971258979020943193104561 31478444234265707394828421)
          ·
            refine ⟨5902208293924820136530329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31478444234265707394828421 5902208293924820136530329)
            ·
              refine ⟨4426656220443615102397747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5902208293924820136530329 4426656220443615102397747)
              ·
                refine ⟨6639984330665422653596621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4426656220443615102397747 6639984330665422653596621)
                ·
                  refine ⟨2489994123999533495098733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6639984330665422653596621 2489994123999533495098733)
                  ·
                    refine ⟨933747796499825060662025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2489994123999533495098733 933747796499825060662025)
                    ·
                      rfl

theorem cell22_2727701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_2727701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2727701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2727701 prefixEnd_2727701 := by exact prefixLift 2727701
  have htrace : WordTrace (prefixWord ++ tailWord_2727701) baseStart_2727701 baseEnd_2727701 := by
    simpa [prefixWord, tailWord_2727701, baseEnd_2727701] using wordTrace_append hprefix tailTrace_2727701
  have hstable : (prefixWord ++ tailWord_2727701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727701).length < 2 ^ (prefixWord ++ tailWord_2727701).sum := by decide
  have hdescent : baseEnd_2727701 < baseStart_2727701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727778 : List Nat := [3, 3, 2, 1, 2, 1, 3, 2, 1, 4]
def baseStart_2727778 : Nat := 118140960795 + 2727778 * 2 ^ 59
def prefixEnd_2727778 : Nat := 4983230072969 + 3 ^ 40 * 2727778 * 2
def baseEnd_2727778 : Nat := 933774155173422526486789

theorem tailTrace_2727778 : CollatzResearch.WordTrace tailWord_2727778 prefixEnd_2727778 933774155173422526486789 := by
  unfold tailWord_2727778
  simp only [CollatzResearch.WordTrace]
  refine ⟨24872559277933412059477997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66326824741155765491941325 24872559277933412059477997)
  ·
    refine ⟨9327209729225029522304249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24872559277933412059477997 9327209729225029522304249)
    ·
      refine ⟨6995407296918772141728187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9327209729225029522304249 6995407296918772141728187)
      ·
        refine ⟨10493110945378158212592281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6995407296918772141728187 10493110945378158212592281)
        ·
          refine ⟨7869833209033618659444211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10493110945378158212592281 7869833209033618659444211)
          ·
            refine ⟨11804749813550427989166317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7869833209033618659444211 11804749813550427989166317)
            ·
              refine ⟨4426781180081410495937369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11804749813550427989166317 4426781180081410495937369)
              ·
                refine ⟨3320085885061057871953027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4426781180081410495937369 3320085885061057871953027)
                ·
                  refine ⟨4980128827591586807929541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3320085885061057871953027 4980128827591586807929541)
                  ·
                    refine ⟨933774155173422526486789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4980128827591586807929541 933774155173422526486789)
                    ·
                      rfl

theorem cell22_2727778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_2727778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2727778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2727778 prefixEnd_2727778 := by exact prefixLift 2727778
  have htrace : WordTrace (prefixWord ++ tailWord_2727778) baseStart_2727778 baseEnd_2727778 := by
    simpa [prefixWord, tailWord_2727778, baseEnd_2727778] using wordTrace_append hprefix tailTrace_2727778
  have hstable : (prefixWord ++ tailWord_2727778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727778).length < 2 ^ (prefixWord ++ tailWord_2727778).sum := by decide
  have hdescent : baseEnd_2727778 < baseStart_2727778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727789 : List Nat := [1, 5, 1, 1, 1, 1, 2, 3, 1, 6]
def baseStart_2727789 : Nat := 118140960795 + 2727789 * 2 ^ 59
def prefixEnd_2727789 : Nat := 4983230072969 + 3 ^ 40 * 2727789 * 2
def baseEnd_2727789 : Nat := 933777920698222164461755

theorem tailTrace_2727789 : CollatzResearch.WordTrace tailWord_2727789 prefixEnd_2727789 933777920698222164461755 := by
  unfold tailWord_2727789
  simp only [CollatzResearch.WordTrace]
  refine ⟨99490638314693797116562421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66327092209795864744374947 99490638314693797116562421)
  ·
    refine ⟨9327247342002543479677727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99490638314693797116562421 9327247342002543479677727)
    ·
      refine ⟨13990871013003815219516591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9327247342002543479677727 13990871013003815219516591)
      ·
        refine ⟨20986306519505722829274887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13990871013003815219516591 20986306519505722829274887)
        ·
          refine ⟨31479459779258584243912331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20986306519505722829274887 31479459779258584243912331)
          ·
            refine ⟨47219189668887876365868497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31479459779258584243912331 47219189668887876365868497)
            ·
              refine ⟨35414392251665907274401373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47219189668887876365868497 35414392251665907274401373)
              ·
                refine ⟨13280397094374715227900515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35414392251665907274401373 13280397094374715227900515)
                ·
                  refine ⟨19920595641562072841850773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13280397094374715227900515 19920595641562072841850773)
                  ·
                    refine ⟨933777920698222164461755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19920595641562072841850773 933777920698222164461755)
                    ·
                      rfl

theorem cell22_2727789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_2727789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2727789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2727789 prefixEnd_2727789 := by exact prefixLift 2727789
  have htrace : WordTrace (prefixWord ++ tailWord_2727789) baseStart_2727789 baseEnd_2727789 := by
    simpa [prefixWord, tailWord_2727789, baseEnd_2727789] using wordTrace_append hprefix tailTrace_2727789
  have hstable : (prefixWord ++ tailWord_2727789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727789).length < 2 ^ (prefixWord ++ tailWord_2727789).sum := by decide
  have hdescent : baseEnd_2727789 < baseStart_2727789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727864 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 4, 5]
def baseStart_2727864 : Nat := 118140960795 + 2727864 * 2 ^ 59
def prefixEnd_2727864 : Nat := 4983230072969 + 3 ^ 40 * 2727864 * 2
def baseEnd_2727864 : Nat := 933803594730946968836525

theorem tailTrace_2727864 : CollatzResearch.WordTrace tailWord_2727864 prefixEnd_2727864 933803594730946968836525 := by
  unfold tailWord_2727864
  simp only [CollatzResearch.WordTrace]
  refine ⟨49746686894711042462771323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66328915859614723283695097 49746686894711042462771323)
  ·
    refine ⟨74620030342066563694156985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49746686894711042462771323 74620030342066563694156985)
    ·
      refine ⟨55965022756549922770617739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74620030342066563694156985 55965022756549922770617739)
      ·
        refine ⟨83947534134824884155926609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55965022756549922770617739 83947534134824884155926609)
        ·
          refine ⟨62960650601118663116944957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83947534134824884155926609 62960650601118663116944957)
          ·
            refine ⟨23610243975419498668854359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62960650601118663116944957 23610243975419498668854359)
            ·
              refine ⟨35415365963129248003281539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23610243975419498668854359 35415365963129248003281539)
              ·
                refine ⟨53123048944693872004922309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35415365963129248003281539 53123048944693872004922309)
                ·
                  refine ⟨9960571677130101000922933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53123048944693872004922309 9960571677130101000922933)
                  ·
                    refine ⟨933803594730946968836525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9960571677130101000922933 933803594730946968836525)
                    ·
                      rfl

theorem cell22_2727864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_2727864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2727864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2727864 prefixEnd_2727864 := by exact prefixLift 2727864
  have htrace : WordTrace (prefixWord ++ tailWord_2727864) baseStart_2727864 baseEnd_2727864 := by
    simpa [prefixWord, tailWord_2727864, baseEnd_2727864] using wordTrace_append hprefix tailTrace_2727864
  have hstable : (prefixWord ++ tailWord_2727864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727864).length < 2 ^ (prefixWord ++ tailWord_2727864).sum := by decide
  have hdescent : baseEnd_2727864 < baseStart_2727864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727870 : List Nat := [4, 2, 1, 1, 1, 3, 2, 4, 1, 3]
def baseStart_2727870 : Nat := 118140960795 + 2727870 * 2 ^ 59
def prefixEnd_2727870 : Nat := 4983230072969 + 3 ^ 40 * 2727870 * 2
def baseEnd_2727870 : Nat := 933805648653564953186507

theorem tailTrace_2727870 : CollatzResearch.WordTrace tailWord_2727870 prefixEnd_2727870 933805648653564953186507 := by
  unfold tailWord_2727870
  simp only [CollatzResearch.WordTrace]
  refine ⟨12436699078425043493782633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66329061751600231966840709 12436699078425043493782633)
  ·
    refine ⟨9327524308818782620336975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12436699078425043493782633 9327524308818782620336975)
    ·
      refine ⟨13991286463228173930505463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9327524308818782620336975 13991286463228173930505463)
      ·
        refine ⟨20986929694842260895758195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13991286463228173930505463 20986929694842260895758195)
        ·
          refine ⟨31480394542263391343637293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20986929694842260895758195 31480394542263391343637293)
          ·
            refine ⟨11805147953348771753863985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31480394542263391343637293 11805147953348771753863985)
            ·
              refine ⟨8853860965011578815397989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11805147953348771753863985 8853860965011578815397989)
              ·
                refine ⟨1660098930939671027887123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8853860965011578815397989 1660098930939671027887123)
                ·
                  refine ⟨2490148396409506541830685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1660098930939671027887123 2490148396409506541830685)
                  ·
                    refine ⟨933805648653564953186507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2490148396409506541830685 933805648653564953186507)
                    ·
                      rfl

theorem cell22_2727870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_2727870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2727870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2727870 prefixEnd_2727870 := by exact prefixLift 2727870
  have htrace : WordTrace (prefixWord ++ tailWord_2727870) baseStart_2727870 baseEnd_2727870 := by
    simpa [prefixWord, tailWord_2727870, baseEnd_2727870] using wordTrace_append hprefix tailTrace_2727870
  have hstable : (prefixWord ++ tailWord_2727870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727870).length < 2 ^ (prefixWord ++ tailWord_2727870).sum := by decide
  have hdescent : baseEnd_2727870 < baseStart_2727870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727986 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 2, 6]
def baseStart_2727986 : Nat := 118140960795 + 2727986 * 2 ^ 59
def prefixEnd_2727986 : Nat := 4983230072969 + 3 ^ 40 * 2727986 * 2
def baseEnd_2727986 : Nat := 933845357824179317286151

theorem tailTrace_2727986 : CollatzResearch.WordTrace tailWord_2727986 prefixEnd_2727986 933845357824179317286151 := by
  unfold tailWord_2727986
  simp only [CollatzResearch.WordTrace]
  refine ⟨24874455873745024940370953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66331882329986733174322541 24874455873745024940370953)
  ·
    refine ⟨18655841905308768705278215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24874455873745024940370953 18655841905308768705278215)
    ·
      refine ⟨27983762857963153057917323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18655841905308768705278215 27983762857963153057917323)
      ·
        refine ⟨41975644286944729586875985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27983762857963153057917323 41975644286944729586875985)
        ·
          refine ⟨31481733215208547190156989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41975644286944729586875985 31481733215208547190156989)
          ·
            refine ⟨11805649955703205196308871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31481733215208547190156989 11805649955703205196308871)
            ·
              refine ⟨17708474933554807794463307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11805649955703205196308871 17708474933554807794463307)
              ·
                refine ⟨26562712400332211691694961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17708474933554807794463307 26562712400332211691694961)
                ·
                  refine ⟨19922034300249158768771221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26562712400332211691694961 19922034300249158768771221)
                  ·
                    refine ⟨933845357824179317286151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19922034300249158768771221 933845357824179317286151)
                    ·
                      rfl

theorem cell22_2727986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_2727986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2727986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2727986 prefixEnd_2727986 := by exact prefixLift 2727986
  have htrace : WordTrace (prefixWord ++ tailWord_2727986) baseStart_2727986 baseEnd_2727986 := by
    simpa [prefixWord, tailWord_2727986, baseEnd_2727986] using wordTrace_append hprefix tailTrace_2727986
  have hstable : (prefixWord ++ tailWord_2727986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727986).length < 2 ^ (prefixWord ++ tailWord_2727986).sum := by decide
  have hdescent : baseEnd_2727986 < baseStart_2727986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728031 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 5, 4]
def baseStart_2728031 : Nat := 118140960795 + 2728031 * 2 ^ 59
def prefixEnd_2728031 : Nat := 4983230072969 + 3 ^ 40 * 2728031 * 2
def baseEnd_2728031 : Nat := 933860762243814199911013

theorem tailTrace_2728031 : CollatzResearch.WordTrace tailWord_2728031 prefixEnd_2728031 933860762243814199911013 := by
  unfold tailWord_2728031
  simp only [CollatzResearch.WordTrace]
  refine ⟨99499464779817072446871947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66332976519878048297914631 99499464779817072446871947)
  ·
    refine ⟨149249197169725608670307921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99499464779817072446871947 149249197169725608670307921)
    ·
      refine ⟨111936897877294206502730941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149249197169725608670307921 111936897877294206502730941)
      ·
        refine ⟨41976336703985327438524103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111936897877294206502730941 41976336703985327438524103)
        ·
          refine ⟨62964505055977991157786155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41976336703985327438524103 62964505055977991157786155)
          ·
            refine ⟨94446757583966986736679233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62964505055977991157786155 94446757583966986736679233)
            ·
              refine ⟨70835068187975240052509425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94446757583966986736679233 70835068187975240052509425)
              ·
                refine ⟨53126301140981430039382069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70835068187975240052509425 53126301140981430039382069)
                ·
                  refine ⟨4980590731967009066192069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53126301140981430039382069 4980590731967009066192069)
                  ·
                    refine ⟨933860762243814199911013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4980590731967009066192069 933860762243814199911013)
                    ·
                      rfl

theorem cell22_2728031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 4].length) (baseStart_2728031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728031 prefixEnd_2728031 := by exact prefixLift 2728031
  have htrace : WordTrace (prefixWord ++ tailWord_2728031) baseStart_2728031 baseEnd_2728031 := by
    simpa [prefixWord, tailWord_2728031, baseEnd_2728031] using wordTrace_append hprefix tailTrace_2728031
  have hstable : (prefixWord ++ tailWord_2728031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728031).length < 2 ^ (prefixWord ++ tailWord_2728031).sum := by decide
  have hdescent : baseEnd_2728031 < baseStart_2728031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728093 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 4, 4]
def baseStart_2728093 : Nat := 118140960795 + 2728093 * 2 ^ 59
def prefixEnd_2728093 : Nat := 4983230072969 + 3 ^ 40 * 2728093 * 2
def baseEnd_2728093 : Nat := 933881986110866704860823

theorem tailTrace_2728093 : CollatzResearch.WordTrace tailWord_2728093 prefixEnd_2728093 933881986110866704860823 := by
  unfold tailWord_2728093
  simp only [CollatzResearch.WordTrace]
  refine ⟨99501726105592457035628933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66334484070394971357085955 99501726105592457035628933)
  ·
    refine ⟨18656573644798585694180425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99501726105592457035628933 18656573644798585694180425)
    ·
      refine ⟨13992430233598939270635319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18656573644798585694180425 13992430233598939270635319)
      ·
        refine ⟨20988645350398408905952979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13992430233598939270635319 20988645350398408905952979)
        ·
          refine ⟨31482968025597613358929469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20988645350398408905952979 31482968025597613358929469)
          ·
            refine ⟨11806113009599105009598551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31482968025597613358929469 11806113009599105009598551)
            ·
              refine ⟨17709169514398657514397827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11806113009599105009598551 17709169514398657514397827)
              ·
                refine ⟨26563754271597986271596741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17709169514398657514397827 26563754271597986271596741)
                ·
                  refine ⟨4980703925924622425924389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26563754271597986271596741 4980703925924622425924389)
                  ·
                    refine ⟨933881986110866704860823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4980703925924622425924389 933881986110866704860823)
                    ·
                      rfl

theorem cell22_2728093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_2728093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728093 prefixEnd_2728093 := by exact prefixLift 2728093
  have htrace : WordTrace (prefixWord ++ tailWord_2728093) baseStart_2728093 baseEnd_2728093 := by
    simpa [prefixWord, tailWord_2728093, baseEnd_2728093] using wordTrace_append hprefix tailTrace_2728093
  have hstable : (prefixWord ++ tailWord_2728093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728093).length < 2 ^ (prefixWord ++ tailWord_2728093).sum := by decide
  have hdescent : baseEnd_2728093 < baseStart_2728093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728095 : List Nat := [1, 1, 2, 6, 1, 1, 2, 1, 4, 3]
def baseStart_2728095 : Nat := 118140960795 + 2728095 * 2 ^ 59
def prefixEnd_2728095 : Nat := 4983230072969 + 3 ^ 40 * 2728095 * 2
def baseEnd_2728095 : Nat := 933882670751739366310817

theorem tailTrace_2728095 : CollatzResearch.WordTrace tailWord_2728095 prefixEnd_2728095 933882670751739366310817 := by
  unfold tailWord_2728095
  simp only [CollatzResearch.WordTrace]
  refine ⟨99501799051585211377201739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66334532701056807584801159 99501799051585211377201739)
  ·
    refine ⟨149252698577377817065802609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99501799051585211377201739 149252698577377817065802609)
    ·
      refine ⟨111939523933033362799351957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149252698577377817065802609 111939523933033362799351957)
      ·
        refine ⟨5247165184360938881219623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 111939523933033362799351957 5247165184360938881219623)
        ·
          refine ⟨7870747776541408321829435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5247165184360938881219623 7870747776541408321829435)
          ·
            refine ⟨11806121664812112482744153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7870747776541408321829435 11806121664812112482744153)
            ·
              refine ⟨8854591248609084362058115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11806121664812112482744153 8854591248609084362058115)
              ·
                refine ⟨13281886872913626543087173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8854591248609084362058115 13281886872913626543087173)
                ·
                  refine ⟨2490353788671304976828845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13281886872913626543087173 2490353788671304976828845)
                  ·
                    refine ⟨933882670751739366310817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2490353788671304976828845 933882670751739366310817)
                    ·
                      rfl

theorem cell22_2728095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 4, 3].length) (baseStart_2728095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728095 prefixEnd_2728095 := by exact prefixLift 2728095
  have htrace : WordTrace (prefixWord ++ tailWord_2728095) baseStart_2728095 baseEnd_2728095 := by
    simpa [prefixWord, tailWord_2728095, baseEnd_2728095] using wordTrace_append hprefix tailTrace_2728095
  have hstable : (prefixWord ++ tailWord_2728095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728095).length < 2 ^ (prefixWord ++ tailWord_2728095).sum := by decide
  have hdescent : baseEnd_2728095 < baseStart_2728095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728097 : List Nat := [1, 2, 3, 3, 1, 3, 3, 2, 4]
def baseStart_2728097 : Nat := 118140960795 + 2728097 * 2 ^ 59
def prefixEnd_2728097 : Nat := 4983230072969 + 3 ^ 40 * 2728097 * 2
def baseEnd_2728097 : Nat := 311294451797537342586937

theorem tailTrace_2728097 : CollatzResearch.WordTrace tailWord_2728097 prefixEnd_2728097 311294451797537342586937 := by
  unfold tailWord_2728097
  simp only [CollatzResearch.WordTrace]
  refine ⟨99501871997577965718774545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66334581331718643812516363 99501871997577965718774545)
  ·
    refine ⟨74626403998183474289080909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99501871997577965718774545 74626403998183474289080909)
    ·
      refine ⟨27984901499318802858405341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74626403998183474289080909 27984901499318802858405341)
      ·
        refine ⟨10494338062244551071902003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27984901499318802858405341 10494338062244551071902003)
        ·
          refine ⟨15741507093366826607853005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10494338062244551071902003 15741507093366826607853005)
          ·
            refine ⟨5903065160012559977944877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15741507093366826607853005 5903065160012559977944877)
            ·
              refine ⟨2213649435004709991729329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5903065160012559977944877 2213649435004709991729329)
              ·
                refine ⟨1660237076253532493796997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2213649435004709991729329 1660237076253532493796997)
                ·
                  refine ⟨311294451797537342586937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1660237076253532493796997 311294451797537342586937)
                  ·
                    rfl

theorem cell22_2728097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 2, 4].length) (baseStart_2728097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728097 prefixEnd_2728097 := by exact prefixLift 2728097
  have htrace : WordTrace (prefixWord ++ tailWord_2728097) baseStart_2728097 baseEnd_2728097 := by
    simpa [prefixWord, tailWord_2728097, baseEnd_2728097] using wordTrace_append hprefix tailTrace_2728097
  have hstable : (prefixWord ++ tailWord_2728097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728097).length < 2 ^ (prefixWord ++ tailWord_2728097).sum := by decide
  have hdescent : baseEnd_2728097 < baseStart_2728097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728123 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 5, 3]
def baseStart_2728123 : Nat := 118140960795 + 2728123 * 2 ^ 59
def prefixEnd_2728123 : Nat := 4983230072969 + 3 ^ 40 * 2728123 * 2
def baseEnd_2728123 : Nat := 933892255723956626610731

theorem tailTrace_2728123 : CollatzResearch.WordTrace tailWord_2728123 prefixEnd_2728123 933892255723956626610731 := by
  unfold tailWord_2728123
  simp only [CollatzResearch.WordTrace]
  refine ⟨99502820295483772159221023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66335213530322514772814015 99502820295483772159221023)
  ·
    refine ⟨149254230443225658238831535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99502820295483772159221023 149254230443225658238831535)
    ·
      refine ⟨223881345664838487358247303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149254230443225658238831535 223881345664838487358247303)
      ·
        refine ⟨335822018497257731037370955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223881345664838487358247303 335822018497257731037370955)
        ·
          refine ⟨503733027745886596556056433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335822018497257731037370955 503733027745886596556056433)
          ·
            refine ⟨377799770809414947417042325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 503733027745886596556056433 377799770809414947417042325)
            ·
              refine ⟨17709364256691325660173859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 377799770809414947417042325 17709364256691325660173859)
              ·
                refine ⟨26564046385036988490260789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17709364256691325660173859 26564046385036988490260789)
                ·
                  refine ⟨2490379348597217670961949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26564046385036988490260789 2490379348597217670961949)
                  ·
                    refine ⟨933892255723956626610731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2490379348597217670961949 933892255723956626610731)
                    ·
                      rfl

theorem cell22_2728123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 5, 3].length) (baseStart_2728123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728123 prefixEnd_2728123 := by exact prefixLift 2728123
  have htrace : WordTrace (prefixWord ++ tailWord_2728123) baseStart_2728123 baseEnd_2728123 := by
    simpa [prefixWord, tailWord_2728123, baseEnd_2728123] using wordTrace_append hprefix tailTrace_2728123
  have hstable : (prefixWord ++ tailWord_2728123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728123).length < 2 ^ (prefixWord ++ tailWord_2728123).sum := by decide
  have hdescent : baseEnd_2728123 < baseStart_2728123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728153 : List Nat := [1, 2, 1, 2, 3, 1, 3, 4, 5]
def baseStart_2728153 : Nat := 118140960795 + 2728153 * 2 ^ 59
def prefixEnd_2728153 : Nat := 4983230072969 + 3 ^ 40 * 2728153 * 2
def baseEnd_2728153 : Nat := 311300841779015516120213

theorem tailTrace_2728153 : CollatzResearch.WordTrace tailWord_2728153 prefixEnd_2728153 311300841779015516120213 := by
  unfold tailWord_2728153
  simp only [CollatzResearch.WordTrace]
  refine ⟨99503914485375087282813113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66335942990250058188542075 99503914485375087282813113)
  ·
    refine ⟨74627935864031315462109835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99503914485375087282813113 74627935864031315462109835)
    ·
      refine ⟨111941903796046973193164753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74627935864031315462109835 111941903796046973193164753)
      ·
        refine ⟨83956427847035229894873565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111941903796046973193164753 83956427847035229894873565)
        ·
          refine ⟨31483660442638211210577587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83956427847035229894873565 31483660442638211210577587)
          ·
            refine ⟨47225490663957316815866381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31483660442638211210577587 47225490663957316815866381)
            ·
              refine ⟨17709558998983993805949893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47225490663957316815866381 17709558998983993805949893)
              ·
                refine ⟨3320542312309498838615605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17709558998983993805949893 3320542312309498838615605)
                ·
                  refine ⟨311300841779015516120213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3320542312309498838615605 311300841779015516120213)
                  ·
                    rfl

theorem cell22_2728153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 5].length) (baseStart_2728153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728153 prefixEnd_2728153 := by exact prefixLift 2728153
  have htrace : WordTrace (prefixWord ++ tailWord_2728153) baseStart_2728153 baseEnd_2728153 := by
    simpa [prefixWord, tailWord_2728153, baseEnd_2728153] using wordTrace_append hprefix tailTrace_2728153
  have hstable : (prefixWord ++ tailWord_2728153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728153).length < 2 ^ (prefixWord ++ tailWord_2728153).sum := by decide
  have hdescent : baseEnd_2728153 < baseStart_2728153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728168 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 1, 7]
def baseStart_2728168 : Nat := 118140960795 + 2728168 * 2 ^ 59
def prefixEnd_2728168 : Nat := 4983230072969 + 3 ^ 40 * 2728168 * 2
def baseEnd_2728168 : Nat := 933907660143591509235593

theorem tailTrace_2728168 : CollatzResearch.WordTrace tailWord_2728168 prefixEnd_2728168 933907660143591509235593 := by
  unfold tailWord_2728168
  simp only [CollatzResearch.WordTrace]
  refine ⟨49752230790160372422304579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66336307720213829896406105 49752230790160372422304579)
  ·
    refine ⟨74628346185240558633456869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49752230790160372422304579 74628346185240558633456869)
    ·
      refine ⟨13992814909732604743773163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74628346185240558633456869 13992814909732604743773163)
      ·
        refine ⟨20989222364598907115659745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13992814909732604743773163 20989222364598907115659745)
        ·
          refine ⟨15741916773449180336744809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20989222364598907115659745 15741916773449180336744809)
          ·
            refine ⟨11806437580086885252558607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15741916773449180336744809 11806437580086885252558607)
            ·
              refine ⟨17709656370130327878837911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11806437580086885252558607 17709656370130327878837911)
              ·
                refine ⟨26564484555195491818256867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17709656370130327878837911 26564484555195491818256867)
                ·
                  refine ⟨39846726832793237727385301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26564484555195491818256867 39846726832793237727385301)
                  ·
                    refine ⟨933907660143591509235593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39846726832793237727385301 933907660143591509235593)
                    ·
                      rfl

theorem cell22_2728168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_2728168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728168 prefixEnd_2728168 := by exact prefixLift 2728168
  have htrace : WordTrace (prefixWord ++ tailWord_2728168) baseStart_2728168 baseEnd_2728168 := by
    simpa [prefixWord, tailWord_2728168, baseEnd_2728168] using wordTrace_append hprefix tailTrace_2728168
  have hstable : (prefixWord ++ tailWord_2728168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728168).length < 2 ^ (prefixWord ++ tailWord_2728168).sum := by decide
  have hdescent : baseEnd_2728168 < baseStart_2728168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728213 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 3, 5]
def baseStart_2728213 : Nat := 118140960795 + 2728213 * 2 ^ 59
def prefixEnd_2728213 : Nat := 4983230072969 + 3 ^ 40 * 2728213 * 2
def baseEnd_2728213 : Nat := 933923064563226391860455

theorem tailTrace_2728213 : CollatzResearch.WordTrace tailWord_2728213 prefixEnd_2728213 933923064563226391860455 := by
  unfold tailWord_2728213
  simp only [CollatzResearch.WordTrace]
  refine ⟨99506102865157717529997293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66337401910105145019998195 99506102865157717529997293)
  ·
    refine ⟨37314788574434144073748985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99506102865157717529997293 37314788574434144073748985)
    ·
      refine ⟨27986091430825608055311739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37314788574434144073748985 27986091430825608055311739)
      ·
        refine ⟨41979137146238412082967609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27986091430825608055311739 41979137146238412082967609)
        ·
          refine ⟨31484352859678809062225707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41979137146238412082967609 31484352859678809062225707)
          ·
            refine ⟨47226529289518213593338561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31484352859678809062225707 47226529289518213593338561)
            ·
              refine ⟨35419896967138660195003921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47226529289518213593338561 35419896967138660195003921)
              ·
                refine ⟨26564922725353995146252941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35419896967138660195003921 26564922725353995146252941)
                ·
                  refine ⟨9961846022007748179844853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26564922725353995146252941 9961846022007748179844853)
                  ·
                    refine ⟨933923064563226391860455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9961846022007748179844853 933923064563226391860455)
                    ·
                      rfl

theorem cell22_2728213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_2728213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728213 prefixEnd_2728213 := by exact prefixLift 2728213
  have htrace : WordTrace (prefixWord ++ tailWord_2728213) baseStart_2728213 baseEnd_2728213 := by
    simpa [prefixWord, tailWord_2728213, baseEnd_2728213] using wordTrace_append hprefix tailTrace_2728213
  have hstable : (prefixWord ++ tailWord_2728213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728213).length < 2 ^ (prefixWord ++ tailWord_2728213).sum := by decide
  have hdescent : baseEnd_2728213 < baseStart_2728213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728215 : List Nat := [1, 1, 3, 4, 1, 3, 2, 1, 6]
def baseStart_2728215 : Nat := 118140960795 + 2728215 * 2 ^ 59
def prefixEnd_2728215 : Nat := 4983230072969 + 3 ^ 40 * 2728215 * 2
def baseEnd_2728215 : Nat := 311307916401366351103483

theorem tailTrace_2728215 : CollatzResearch.WordTrace tailWord_2728215 prefixEnd_2728215 311307916401366351103483 := by
  unfold tailWord_2728215
  simp only [CollatzResearch.WordTrace]
  refine ⟨99506175811150471871570099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66337450540766981247713399 99506175811150471871570099)
  ·
    refine ⟨149259263716725707807355149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99506175811150471871570099 149259263716725707807355149)
    ·
      refine ⟨55972223893772140427758181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149259263716725707807355149 55972223893772140427758181)
      ·
        refine ⟨10494791980082276330204659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55972223893772140427758181 10494791980082276330204659)
        ·
          refine ⟨15742187970123414495306989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10494791980082276330204659 15742187970123414495306989)
          ·
            refine ⟨5903320488796280435740121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15742187970123414495306989 5903320488796280435740121)
            ·
              refine ⟨4427490366597210326805091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5903320488796280435740121 4427490366597210326805091)
              ·
                refine ⟨6641235549895815490207637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4427490366597210326805091 6641235549895815490207637)
                ·
                  refine ⟨311307916401366351103483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6641235549895815490207637 311307916401366351103483)
                  ·
                    rfl

theorem cell22_2728215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 6].length) (baseStart_2728215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728215 prefixEnd_2728215 := by exact prefixLift 2728215
  have htrace : WordTrace (prefixWord ++ tailWord_2728215) baseStart_2728215 baseEnd_2728215 := by
    simpa [prefixWord, tailWord_2728215, baseEnd_2728215] using wordTrace_append hprefix tailTrace_2728215
  have hstable : (prefixWord ++ tailWord_2728215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728215).length < 2 ^ (prefixWord ++ tailWord_2728215).sum := by decide
  have hdescent : baseEnd_2728215 < baseStart_2728215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728234 : List Nat := [3, 1, 4, 2, 2, 1, 2, 2, 1, 4]
def baseStart_2728234 : Nat := 118140960795 + 2728234 * 2 ^ 59
def prefixEnd_2728234 : Nat := 4983230072969 + 3 ^ 40 * 2728234 * 2
def baseEnd_2728234 : Nat := 933930253292389337085391

theorem tailTrace_2728234 : CollatzResearch.WordTrace tailWord_2728234 prefixEnd_2728234 933930253292389337085391 := by
  unfold tailWord_2728234
  simp only [CollatzResearch.WordTrace]
  refine ⟨24876717199520409529127939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66337912532054425411007837 24876717199520409529127939)
  ·
    refine ⟨37315075799280614293691909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24876717199520409529127939 37315075799280614293691909)
    ·
      refine ⟨6996576712365115180067233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37315075799280614293691909 6996576712365115180067233)
      ·
        refine ⟨5247432534273836385050425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6996576712365115180067233 5247432534273836385050425)
        ·
          refine ⟨3935574400705377288787819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5247432534273836385050425 3935574400705377288787819)
          ·
            refine ⟨5903361601058065933181729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3935574400705377288787819 5903361601058065933181729)
            ·
              refine ⟨4427521200793549449886297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5903361601058065933181729 4427521200793549449886297)
              ·
                refine ⟨3320640900595162087414723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4427521200793549449886297 3320640900595162087414723)
                ·
                  refine ⟨4980961350892743131122085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3320640900595162087414723 4980961350892743131122085)
                  ·
                    refine ⟨933930253292389337085391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4980961350892743131122085 933930253292389337085391)
                    ·
                      rfl

theorem cell22_2728234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_2728234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728234 prefixEnd_2728234 := by exact prefixLift 2728234
  have htrace : WordTrace (prefixWord ++ tailWord_2728234) baseStart_2728234 baseEnd_2728234 := by
    simpa [prefixWord, tailWord_2728234, baseEnd_2728234] using wordTrace_append hprefix tailTrace_2728234
  have hstable : (prefixWord ++ tailWord_2728234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728234).length < 2 ^ (prefixWord ++ tailWord_2728234).sum := by decide
  have hdescent : baseEnd_2728234 < baseStart_2728234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728243 : List Nat := [1, 1, 1, 2, 5, 1, 3, 8]
def baseStart_2728243 : Nat := 118140960795 + 2728243 * 2 ^ 59
def prefixEnd_2728243 : Nat := 4983230072969 + 3 ^ 40 * 2728243 * 2
def baseEnd_2728243 : Nat := 103770370464035145956707

theorem tailTrace_2728243 : CollatzResearch.WordTrace tailWord_2728243 prefixEnd_2728243 103770370464035145956707 := by
  unfold tailWord_2728243
  simp only [CollatzResearch.WordTrace]
  refine ⟨99507197055049032653589383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66338131370032688435726255 99507197055049032653589383)
  ·
    refine ⟨149260795582573548980384075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99507197055049032653589383 149260795582573548980384075)
    ·
      refine ⟨223891193373860323470576113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149260795582573548980384075 223891193373860323470576113)
      ·
        refine ⟨167918395030395242602932085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223891193373860323470576113 167918395030395242602932085)
        ·
          refine ⟨15742349534099553994024883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 167918395030395242602932085 15742349534099553994024883)
          ·
            refine ⟨23613524301149330991037325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15742349534099553994024883 23613524301149330991037325)
            ·
              refine ⟨8855071612930999121638997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23613524301149330991037325 8855071612930999121638997)
              ·
                refine ⟨103770370464035145956707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8855071612930999121638997 103770370464035145956707)
                ·
                  rfl

theorem cell22_2728243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 8].length) (baseStart_2728243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728243 prefixEnd_2728243 := by exact prefixLift 2728243
  have htrace : WordTrace (prefixWord ++ tailWord_2728243) baseStart_2728243 baseEnd_2728243 := by
    simpa [prefixWord, tailWord_2728243, baseEnd_2728243] using wordTrace_append hprefix tailTrace_2728243
  have hstable : (prefixWord ++ tailWord_2728243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728243).length < 2 ^ (prefixWord ++ tailWord_2728243).sum := by decide
  have hdescent : baseEnd_2728243 < baseStart_2728243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728245 : List Nat := [1, 3, 3, 1, 2, 1, 2, 3, 2, 4]
def baseStart_2728245 : Nat := 118140960795 + 2728245 * 2 ^ 59
def prefixEnd_2728245 : Nat := 4983230072969 + 3 ^ 40 * 2728245 * 2
def baseEnd_2728245 : Nat := 933934018817188975060357

theorem tailTrace_2728245 : CollatzResearch.WordTrace tailWord_2728245 prefixEnd_2728245 933934018817188975060357 := by
  unfold tailWord_2728245
  simp only [CollatzResearch.WordTrace]
  refine ⟨99507270001041786995162189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66338180000694524663441459 99507270001041786995162189)
  ·
    refine ⟨37315226250390670123185821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99507270001041786995162189 37315226250390670123185821)
    ·
      refine ⟨13993209843896501296194683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37315226250390670123185821 13993209843896501296194683)
      ·
        refine ⟨20989814765844751944292025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13993209843896501296194683 20989814765844751944292025)
        ·
          refine ⟨15742361074383563958219019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20989814765844751944292025 15742361074383563958219019)
          ·
            refine ⟨23613541611575345937328529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15742361074383563958219019 23613541611575345937328529)
            ·
              refine ⟨17710156208681509452996397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23613541611575345937328529 17710156208681509452996397)
              ·
                refine ⟨6641308578255566044873649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17710156208681509452996397 6641308578255566044873649)
                ·
                  refine ⟨4980981433691674533655237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6641308578255566044873649 4980981433691674533655237)
                  ·
                    refine ⟨933934018817188975060357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4980981433691674533655237 933934018817188975060357)
                    ·
                      rfl

theorem cell22_2728245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_2728245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728245 prefixEnd_2728245 := by exact prefixLift 2728245
  have htrace : WordTrace (prefixWord ++ tailWord_2728245) baseStart_2728245 baseEnd_2728245 := by
    simpa [prefixWord, tailWord_2728245, baseEnd_2728245] using wordTrace_append hprefix tailTrace_2728245
  have hstable : (prefixWord ++ tailWord_2728245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728245).length < 2 ^ (prefixWord ++ tailWord_2728245).sum := by decide
  have hdescent : baseEnd_2728245 < baseStart_2728245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728249 : List Nat := [1, 2, 1, 6, 1, 3, 1, 3, 4]
def baseStart_2728249 : Nat := 118140960795 + 2728249 * 2 ^ 59
def prefixEnd_2728249 : Nat := 4983230072969 + 3 ^ 40 * 2728249 * 2
def baseEnd_2728249 : Nat := 311311796032978099320115

theorem tailTrace_2728249 : CollatzResearch.WordTrace tailWord_2728249 prefixEnd_2728249 311311796032978099320115 := by
  unfold tailWord_2728249
  simp only [CollatzResearch.WordTrace]
  refine ⟨99507415893027295678307801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66338277262018197118871867 99507415893027295678307801)
  ·
    refine ⟨74630561919770471758730851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99507415893027295678307801 74630561919770471758730851)
    ·
      refine ⟨111945842879655707638096277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74630561919770471758730851 111945842879655707638096277)
      ·
        refine ⟨5247461384983861295535763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 111945842879655707638096277 5247461384983861295535763)
        ·
          refine ⟨7871192077475791943303645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5247461384983861295535763 7871192077475791943303645)
          ·
            refine ⟨2951697029053421978738867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7871192077475791943303645 2951697029053421978738867)
            ·
              refine ⟨4427545543580132968108301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2951697029053421978738867 4427545543580132968108301)
              ·
                refine ⟨1660329578842549863040613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4427545543580132968108301 1660329578842549863040613)
                ·
                  refine ⟨311311796032978099320115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1660329578842549863040613 311311796032978099320115)
                  ·
                    rfl

theorem cell22_2728249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 3, 4].length) (baseStart_2728249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728249 prefixEnd_2728249 := by exact prefixLift 2728249
  have htrace : WordTrace (prefixWord ++ tailWord_2728249) baseStart_2728249 baseEnd_2728249 := by
    simpa [prefixWord, tailWord_2728249, baseEnd_2728249] using wordTrace_append hprefix tailTrace_2728249
  have hstable : (prefixWord ++ tailWord_2728249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728249).length < 2 ^ (prefixWord ++ tailWord_2728249).sum := by decide
  have hdescent : baseEnd_2728249 < baseStart_2728249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728275 : List Nat := [1, 1, 1, 2, 1, 1, 4, 5, 3, 3]
def baseStart_2728275 : Nat := 118140960795 + 2728275 * 2 ^ 59
def prefixEnd_2728275 : Nat := 4983230072969 + 3 ^ 40 * 2728275 * 2
def baseEnd_2728275 : Nat := 933944288430278896810265

theorem tailTrace_2728275 : CollatzResearch.WordTrace tailWord_2728275 prefixEnd_2728275 933944288430278896810265 := by
  unfold tailWord_2728275
  simp only [CollatzResearch.WordTrace]
  refine ⟨99508364190933102118754279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66338909460622068079169519 99508364190933102118754279)
  ·
    refine ⟨149262546286399653178131419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99508364190933102118754279 149262546286399653178131419)
    ·
      refine ⟨223893819429599479767197129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149262546286399653178131419 223893819429599479767197129)
      ·
        refine ⟨167920364572199609825397847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223893819429599479767197129 167920364572199609825397847)
        ·
          refine ⟨251880546858299414738096771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167920364572199609825397847 251880546858299414738096771)
          ·
            refine ⟨377820820287449122107145157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251880546858299414738096771 377820820287449122107145157)
            ·
              refine ⟨70841403803896710395089717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 377820820287449122107145157 70841403803896710395089717)
              ·
                refine ⟨6641381606615316599539661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70841403803896710395089717 6641381606615316599539661)
                ·
                  refine ⟨2490518102480743724827373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6641381606615316599539661 2490518102480743724827373)
                  ·
                    refine ⟨933944288430278896810265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2490518102480743724827373 933944288430278896810265)
                    ·
                      rfl

theorem cell22_2728275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 3, 3].length) (baseStart_2728275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728275 prefixEnd_2728275 := by exact prefixLift 2728275
  have htrace : WordTrace (prefixWord ++ tailWord_2728275) baseStart_2728275 baseEnd_2728275 := by
    simpa [prefixWord, tailWord_2728275, baseEnd_2728275] using wordTrace_append hprefix tailTrace_2728275
  have hstable : (prefixWord ++ tailWord_2728275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728275).length < 2 ^ (prefixWord ++ tailWord_2728275).sum := by decide
  have hdescent : baseEnd_2728275 < baseStart_2728275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728303 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 3, 7]
def baseStart_2728303 : Nat := 118140960795 + 2728303 * 2 ^ 59
def prefixEnd_2728303 : Nat := 4983230072969 + 3 ^ 40 * 2728303 * 2
def baseEnd_2728303 : Nat := 933953873402496157110179

theorem tailTrace_2728303 : CollatzResearch.WordTrace tailWord_2728303 prefixEnd_2728303 933953873402496157110179 := by
  unfold tailWord_2728303
  simp only [CollatzResearch.WordTrace]
  refine ⟨99509385434831662900773563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66339590289887775267182375 99509385434831662900773563)
  ·
    refine ⟨149264078152247494351160345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99509385434831662900773563 149264078152247494351160345)
    ·
      refine ⟨111948058614185620763370259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149264078152247494351160345 111948058614185620763370259)
      ·
        refine ⟨167922087921278431145055389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111948058614185620763370259 167922087921278431145055389)
        ·
          refine ⟨62970782970479411679395771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167922087921278431145055389 62970782970479411679395771)
          ·
            refine ⟨94456174455719117519093657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62970782970479411679395771 94456174455719117519093657)
            ·
              refine ⟨70842130841789338139320243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94456174455719117519093657 70842130841789338139320243)
              ·
                refine ⟨106263196262684007208980365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70842130841789338139320243 106263196262684007208980365)
                ·
                  refine ⟨39848698598506502703367637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106263196262684007208980365 39848698598506502703367637)
                  ·
                    refine ⟨933953873402496157110179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39848698598506502703367637 933953873402496157110179)
                    ·
                      rfl

theorem cell22_2728303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 7].length) (baseStart_2728303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728303 prefixEnd_2728303 := by exact prefixLift 2728303
  have htrace : WordTrace (prefixWord ++ tailWord_2728303) baseStart_2728303 baseEnd_2728303 := by
    simpa [prefixWord, tailWord_2728303, baseEnd_2728303] using wordTrace_append hprefix tailTrace_2728303
  have hstable : (prefixWord ++ tailWord_2728303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728303).length < 2 ^ (prefixWord ++ tailWord_2728303).sum := by decide
  have hdescent : baseEnd_2728303 < baseStart_2728303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728369 : List Nat := [1, 2, 2, 4, 1, 2, 4, 1, 1, 4]
def baseStart_2728369 : Nat := 118140960795 + 2728369 * 2 ^ 59
def prefixEnd_2728369 : Nat := 4983230072969 + 3 ^ 40 * 2728369 * 2
def baseEnd_2728369 : Nat := 933976466551293984959977

theorem tailTrace_2728369 : CollatzResearch.WordTrace tailWord_2728369 prefixEnd_2728369 933976466551293984959977 := by
  unfold tailWord_2728369
  simp only [CollatzResearch.WordTrace]
  refine ⟨99511792652592556172676161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66341195101728370781784107 99511792652592556172676161)
  ·
    refine ⟨74633844489444417129507121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99511792652592556172676161 74633844489444417129507121)
    ·
      refine ⟨55975383367083312847130341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74633844489444417129507121 55975383367083312847130341)
      ·
        refine ⟨10495384381328121158836939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55975383367083312847130341 10495384381328121158836939)
        ·
          refine ⟨15743076571992181738255409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10495384381328121158836939 15743076571992181738255409)
          ·
            refine ⟨11807307428994136303691557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15743076571992181738255409 11807307428994136303691557)
            ·
              refine ⟨2213870142936400556942167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11807307428994136303691557 2213870142936400556942167)
              ·
                refine ⟨3320805214404600835413251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2213870142936400556942167 3320805214404600835413251)
                ·
                  refine ⟨4981207821606901253119877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3320805214404600835413251 4981207821606901253119877)
                  ·
                    refine ⟨933976466551293984959977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4981207821606901253119877 933976466551293984959977)
                    ·
                      rfl

theorem cell22_2728369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 1, 4].length) (baseStart_2728369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728369 prefixEnd_2728369 := by exact prefixLift 2728369
  have htrace : WordTrace (prefixWord ++ tailWord_2728369) baseStart_2728369 baseEnd_2728369 := by
    simpa [prefixWord, tailWord_2728369, baseEnd_2728369] using wordTrace_append hprefix tailTrace_2728369
  have hstable : (prefixWord ++ tailWord_2728369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728369).length < 2 ^ (prefixWord ++ tailWord_2728369).sum := by decide
  have hdescent : baseEnd_2728369 < baseStart_2728369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728410 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 2, 7]
def baseStart_2728410 : Nat := 118140960795 + 2728410 * 2 ^ 59
def prefixEnd_2728410 : Nat := 4983230072969 + 3 ^ 40 * 2728410 * 2
def baseEnd_2728410 : Nat := 933990501689183544684851

theorem tailTrace_2728410 : CollatzResearch.WordTrace tailWord_2728410 prefixEnd_2728410 933990501689183544684851 := by
  unfold tailWord_2728410
  simp only [CollatzResearch.WordTrace]
  refine ⟨24878322011361005043729671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66342192030296013449945789 24878322011361005043729671)
  ·
    refine ⟨37317483017041507565594507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24878322011361005043729671 37317483017041507565594507)
    ·
      refine ⟨55976224525562261348391761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37317483017041507565594507 55976224525562261348391761)
      ·
        refine ⟨41982168394171696011293821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55976224525562261348391761 41982168394171696011293821)
        ·
          refine ⟨15743313147814386004235183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41982168394171696011293821 15743313147814386004235183)
          ·
            refine ⟨23614969721721579006352775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15743313147814386004235183 23614969721721579006352775)
            ·
              refine ⟨35422454582582368509529163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23614969721721579006352775 35422454582582368509529163)
              ·
                refine ⟨53133681873873552764293745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35422454582582368509529163 53133681873873552764293745)
                ·
                  refine ⟨39850261405405164573220309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53133681873873552764293745 39850261405405164573220309)
                  ·
                    refine ⟨933990501689183544684851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39850261405405164573220309 933990501689183544684851)
                    ·
                      rfl

theorem cell22_2728410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_2728410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728410 prefixEnd_2728410 := by exact prefixLift 2728410
  have htrace : WordTrace (prefixWord ++ tailWord_2728410) baseStart_2728410 baseEnd_2728410 := by
    simpa [prefixWord, tailWord_2728410, baseEnd_2728410] using wordTrace_append hprefix tailTrace_2728410
  have hstable : (prefixWord ++ tailWord_2728410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728410).length < 2 ^ (prefixWord ++ tailWord_2728410).sum := by decide
  have hdescent : baseEnd_2728410 < baseStart_2728410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728440 : List Nat := [2, 1, 2, 1, 1, 4, 1, 3, 7]
def baseStart_2728440 : Nat := 118140960795 + 2728440 * 2 ^ 59
def prefixEnd_2728440 : Nat := 4983230072969 + 3 ^ 40 * 2728440 * 2
def baseEnd_2728440 : Nat := 311333590434091155478253

theorem tailTrace_2728440 : CollatzResearch.WordTrace tailWord_2728440 prefixEnd_2728440 311333590434091155478253 := by
  unfold tailWord_2728440
  simp only [CollatzResearch.WordTrace]
  refine ⟨49757191117667667649255387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66342921490223556865673849 49757191117667667649255387)
  ·
    refine ⟨74635786676501501473883081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49757191117667667649255387 74635786676501501473883081)
    ·
      refine ⟨55976840007376126105412311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74635786676501501473883081 55976840007376126105412311)
      ·
        refine ⟨83965260011064189158118467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55976840007376126105412311 83965260011064189158118467)
        ·
          refine ⟨125947890016596283737177701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83965260011064189158118467 125947890016596283737177701)
          ·
            refine ⟨23615229378111803200720819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125947890016596283737177701 23615229378111803200720819)
            ·
              refine ⟨35422844067167704801081229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23615229378111803200720819 35422844067167704801081229)
              ·
                refine ⟨13283566525187889300405461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35422844067167704801081229 13283566525187889300405461)
                ·
                  refine ⟨311333590434091155478253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13283566525187889300405461 311333590434091155478253)
                  ·
                    rfl

theorem cell22_2728440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 7].length) (baseStart_2728440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728440 prefixEnd_2728440 := by exact prefixLift 2728440
  have htrace : WordTrace (prefixWord ++ tailWord_2728440) baseStart_2728440 baseEnd_2728440 := by
    simpa [prefixWord, tailWord_2728440, baseEnd_2728440] using wordTrace_append hprefix tailTrace_2728440
  have hstable : (prefixWord ++ tailWord_2728440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728440).length < 2 ^ (prefixWord ++ tailWord_2728440).sum := by decide
  have hdescent : baseEnd_2728440 < baseStart_2728440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728450 : List Nat := [3, 4, 1, 2, 2, 2, 2, 1, 2, 3]
def baseStart_2728450 : Nat := 118140960795 + 2728450 * 2 ^ 59
def prefixEnd_2728450 : Nat := 4983230072969 + 3 ^ 40 * 2728450 * 2
def baseEnd_2728450 : Nat := 934004194506636773684729

theorem tailTrace_2728450 : CollatzResearch.WordTrace tailWord_2728450 prefixEnd_2728450 934004194506636773684729 := by
  unfold tailWord_2728450
  simp only [CollatzResearch.WordTrace]
  refine ⟨24878686741324776751593701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66343164643532738004249869 24878686741324776751593701)
  ·
    refine ⟨4664753763998395640923819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24878686741324776751593701 4664753763998395640923819)
    ·
      refine ⟨6997130645997593461385729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4664753763998395640923819 6997130645997593461385729)
      ·
        refine ⟨5247847984498195096039297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6997130645997593461385729 5247847984498195096039297)
        ·
          refine ⟨3935885988373646322029473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5247847984498195096039297 3935885988373646322029473)
          ·
            refine ⟨2951914491280234741522105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3935885988373646322029473 2951914491280234741522105)
            ·
              refine ⟨2213935868460176056141579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2951914491280234741522105 2213935868460176056141579)
              ·
                refine ⟨3320903802690264084212369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2213935868460176056141579 3320903802690264084212369)
                ·
                  refine ⟨2490677852017698063159277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3320903802690264084212369 2490677852017698063159277)
                  ·
                    refine ⟨934004194506636773684729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2490677852017698063159277 934004194506636773684729)
                    ·
                      rfl

theorem cell22_2728450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_2728450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728450 prefixEnd_2728450 := by exact prefixLift 2728450
  have htrace : WordTrace (prefixWord ++ tailWord_2728450) baseStart_2728450 baseEnd_2728450 := by
    simpa [prefixWord, tailWord_2728450, baseEnd_2728450] using wordTrace_append hprefix tailTrace_2728450
  have hstable : (prefixWord ++ tailWord_2728450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728450).length < 2 ^ (prefixWord ++ tailWord_2728450).sum := by decide
  have hdescent : baseEnd_2728450 < baseStart_2728450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728517 : List Nat := [1, 3, 1, 1, 1, 5, 1, 3, 1, 5]
def baseStart_2728517 : Nat := 118140960795 + 2728517 * 2 ^ 59
def prefixEnd_2728517 : Nat := 4983230072969 + 3 ^ 40 * 2728517 * 2
def baseEnd_2728517 : Nat := 934027129975870932259523

theorem tailTrace_2728517 : CollatzResearch.WordTrace tailWord_2728517 prefixEnd_2728517 934027129975870932259523 := by
  unfold tailWord_2728517
  simp only [CollatzResearch.WordTrace]
  refine ⟨99517190656056377449063805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66344793770704251632709203 99517190656056377449063805)
  ·
    refine ⟨37318946496021141543398927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99517190656056377449063805 37318946496021141543398927)
    ·
      refine ⟨55978419744031712315098391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37318946496021141543398927 55978419744031712315098391)
      ·
        refine ⟨83967629616047568472647587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55978419744031712315098391 83967629616047568472647587)
        ·
          refine ⟨125951444424071352708971381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83967629616047568472647587 125951444424071352708971381)
          ·
            refine ⟨11807947914756689316466067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125951444424071352708971381 11807947914756689316466067)
            ·
              refine ⟨17711921872135033974699101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11807947914756689316466067 17711921872135033974699101)
              ·
                refine ⟨6641970702050637740512163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17711921872135033974699101 6641970702050637740512163)
                ·
                  refine ⟨9962956053075956610768245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6641970702050637740512163 9962956053075956610768245)
                  ·
                    refine ⟨934027129975870932259523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9962956053075956610768245 934027129975870932259523)
                    ·
                      rfl

theorem cell22_2728517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_2728517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728517 prefixEnd_2728517 := by exact prefixLift 2728517
  have htrace : WordTrace (prefixWord ++ tailWord_2728517) baseStart_2728517 baseEnd_2728517 := by
    simpa [prefixWord, tailWord_2728517, baseEnd_2728517] using wordTrace_append hprefix tailTrace_2728517
  have hstable : (prefixWord ++ tailWord_2728517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728517).length < 2 ^ (prefixWord ++ tailWord_2728517).sum := by decide
  have hdescent : baseEnd_2728517 < baseStart_2728517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728542 : List Nat := [4, 4, 1, 2, 2, 1, 1, 2, 5]
def baseStart_2728542 : Nat := 118140960795 + 2728542 * 2 ^ 59
def prefixEnd_2728542 : Nat := 4983230072969 + 3 ^ 40 * 2728542 * 2
def baseEnd_2728542 : Nat := 311345229328926400128149

theorem tailTrace_2728542 : CollatzResearch.WordTrace tailWord_2728542 prefixEnd_2728542 311345229328926400128149 := by
  unfold tailWord_2728542
  simp only [CollatzResearch.WordTrace]
  refine ⟨12439762810120725839840485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66345401653977204479149253 12439762810120725839840485)
  ·
    refine ⟨2332455526897636094970091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12439762810120725839840485 2332455526897636094970091)
    ·
      refine ⟨3498683290346454142455137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2332455526897636094970091 3498683290346454142455137)
      ·
        refine ⟨2624012467759840606841353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3498683290346454142455137 2624012467759840606841353)
        ·
          refine ⟨1968009350819880455131015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2624012467759840606841353 1968009350819880455131015)
          ·
            refine ⟨2952014026229820682696523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1968009350819880455131015 2952014026229820682696523)
            ·
              refine ⟨4428021039344731024044785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2952014026229820682696523 4428021039344731024044785)
              ·
                refine ⟨3321015779508548268033589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4428021039344731024044785 3321015779508548268033589)
                ·
                  refine ⟨311345229328926400128149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3321015779508548268033589 311345229328926400128149)
                  ·
                    rfl

theorem cell22_2728542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_2728542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728542 prefixEnd_2728542 := by exact prefixLift 2728542
  have htrace : WordTrace (prefixWord ++ tailWord_2728542) baseStart_2728542 baseEnd_2728542 := by
    simpa [prefixWord, tailWord_2728542, baseEnd_2728542] using wordTrace_append hprefix tailTrace_2728542
  have hstable : (prefixWord ++ tailWord_2728542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728542).length < 2 ^ (prefixWord ++ tailWord_2728542).sum := by decide
  have hdescent : baseEnd_2728542 < baseStart_2728542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728579 : List Nat := [1, 1, 1, 3, 3, 1, 4, 2, 3, 3]
def baseStart_2728579 : Nat := 118140960795 + 2728579 * 2 ^ 59
def prefixEnd_2728579 : Nat := 4983230072969 + 3 ^ 40 * 2728579 * 2
def baseEnd_2728579 : Nat := 934048353842923437209333

theorem tailTrace_2728579 : CollatzResearch.WordTrace tailWord_2728579 prefixEnd_2728579 934048353842923437209333 := by
  unfold tailWord_2728579
  simp only [CollatzResearch.WordTrace]
  refine ⟨99519451981831762037820791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66346301321221174691880527 99519451981831762037820791)
  ·
    refine ⟨149279177972747643056731187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99519451981831762037820791 149279177972747643056731187)
    ·
      refine ⟨223918766959121464585096781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149279177972747643056731187 223918766959121464585096781)
      ·
        refine ⟨83969537609670549219411293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223918766959121464585096781 83969537609670549219411293)
        ·
          refine ⟨31488576603626455957279235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83969537609670549219411293 31488576603626455957279235)
          ·
            refine ⟨47232864905439683935918853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31488576603626455957279235 47232864905439683935918853)
            ·
              refine ⟨8856162169769940737984785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47232864905439683935918853 8856162169769940737984785)
              ·
                refine ⟨6642121627327455553488589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8856162169769940737984785 6642121627327455553488589)
                ·
                  refine ⟨2490795610247795832558221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6642121627327455553488589 2490795610247795832558221)
                  ·
                    refine ⟨934048353842923437209333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2490795610247795832558221 934048353842923437209333)
                    ·
                      rfl

theorem cell22_2728579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 3, 3].length) (baseStart_2728579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728579 prefixEnd_2728579 := by exact prefixLift 2728579
  have htrace : WordTrace (prefixWord ++ tailWord_2728579) baseStart_2728579 baseEnd_2728579 := by
    simpa [prefixWord, tailWord_2728579, baseEnd_2728579] using wordTrace_append hprefix tailTrace_2728579
  have hstable : (prefixWord ++ tailWord_2728579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728579).length < 2 ^ (prefixWord ++ tailWord_2728579).sum := by decide
  have hdescent : baseEnd_2728579 < baseStart_2728579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728639 : List Nat := [1, 1, 2, 2, 2, 5, 1, 1, 3, 4]
def baseStart_2728639 : Nat := 118140960795 + 2728639 * 2 ^ 59
def prefixEnd_2728639 : Nat := 4983230072969 + 3 ^ 40 * 2728639 * 2
def baseEnd_2728639 : Nat := 934068893069103280709149

theorem tailTrace_2728639 : CollatzResearch.WordTrace tailWord_2728639 prefixEnd_2728639 934068893069103280709149 := by
  unfold tailWord_2728639
  simp only [CollatzResearch.WordTrace]
  refine ⟨99521640361614392285004971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66347760241076261523336647 99521640361614392285004971)
  ·
    refine ⟨149282460542421588427507457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99521640361614392285004971 149282460542421588427507457)
    ·
      refine ⟨111961845406816191320630593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149282460542421588427507457 111961845406816191320630593)
      ·
        refine ⟨83971384055112143490472945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111961845406816191320630593 83971384055112143490472945)
        ·
          refine ⟨62978538041334107617854709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83971384055112143490472945 62978538041334107617854709)
          ·
            refine ⟨5904237941375072589173879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62978538041334107617854709 5904237941375072589173879)
            ·
              refine ⟨8856356912062608883760819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5904237941375072589173879 8856356912062608883760819)
              ·
                refine ⟨13284535368093913325641229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8856356912062608883760819 13284535368093913325641229)
                ·
                  refine ⟨4981700763035217497115461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13284535368093913325641229 4981700763035217497115461)
                  ·
                    refine ⟨934068893069103280709149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4981700763035217497115461 934068893069103280709149)
                    ·
                      rfl

theorem cell22_2728639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 4].length) (baseStart_2728639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728639 prefixEnd_2728639 := by exact prefixLift 2728639
  have htrace : WordTrace (prefixWord ++ tailWord_2728639) baseStart_2728639 baseEnd_2728639 := by
    simpa [prefixWord, tailWord_2728639, baseEnd_2728639] using wordTrace_append hprefix tailTrace_2728639
  have hstable : (prefixWord ++ tailWord_2728639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728639).length < 2 ^ (prefixWord ++ tailWord_2728639).sum := by decide
  have hdescent : baseEnd_2728639 < baseStart_2728639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728671 : List Nat := [1, 1, 2, 3, 2, 4, 1, 4, 4]
def baseStart_2728671 : Nat := 118140960795 + 2728671 * 2 ^ 59
def prefixEnd_2728671 : Nat := 4983230072969 + 3 ^ 40 * 2728671 * 2
def baseEnd_2728671 : Nat := 311359949107688621303017

theorem tailTrace_2728671 : CollatzResearch.WordTrace tailWord_2728671 prefixEnd_2728671 311359949107688621303017 := by
  unfold tailWord_2728671
  simp only [CollatzResearch.WordTrace]
  refine ⟨99522807497498461750169867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66348538331665641166779911 99522807497498461750169867)
  ·
    refine ⟨149284211246247692625254801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99522807497498461750169867 149284211246247692625254801)
    ·
      refine ⟨111963158434685769468941101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149284211246247692625254801 111963158434685769468941101)
      ·
        refine ⟨41986184413007163550852913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111963158434685769468941101 41986184413007163550852913)
        ·
          refine ⟨31489638309755372663139685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41986184413007163550852913 31489638309755372663139685)
          ·
            refine ⟨5904307183079132374338691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31489638309755372663139685 5904307183079132374338691)
            ·
              refine ⟨8856460774618698561508037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5904307183079132374338691 8856460774618698561508037)
              ·
                refine ⟨1660586395241005980282757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8856460774618698561508037 1660586395241005980282757)
                ·
                  refine ⟨311359949107688621303017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1660586395241005980282757 311359949107688621303017)
                  ·
                    rfl

theorem cell22_2728671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 4, 4].length) (baseStart_2728671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728671 prefixEnd_2728671 := by exact prefixLift 2728671
  have htrace : WordTrace (prefixWord ++ tailWord_2728671) baseStart_2728671 baseEnd_2728671 := by
    simpa [prefixWord, tailWord_2728671, baseEnd_2728671] using wordTrace_append hprefix tailTrace_2728671
  have hstable : (prefixWord ++ tailWord_2728671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728671).length < 2 ^ (prefixWord ++ tailWord_2728671).sum := by decide
  have hdescent : baseEnd_2728671 < baseStart_2728671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728686 : List Nat := [4, 1, 2, 1, 1, 4, 2, 1, 1, 5]
def baseStart_2728686 : Nat := 118140960795 + 2728686 * 2 ^ 59
def prefixEnd_2728686 : Nat := 4983230072969 + 3 ^ 40 * 2728686 * 2
def baseEnd_2728686 : Nat := 934084982129610824784005

theorem tailTrace_2728686 : CollatzResearch.WordTrace tailWord_2728686 prefixEnd_2728686 934084982129610824784005 := by
  unfold tailWord_2728686
  simp only [CollatzResearch.WordTrace]
  refine ⟨12440419324055514913995739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66348903061629412874643941 12440419324055514913995739)
  ·
    refine ⟨18660628986083272370993609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12440419324055514913995739 18660628986083272370993609)
    ·
      refine ⟨13995471739562454278245207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18660628986083272370993609 13995471739562454278245207)
      ·
        refine ⟨20993207609343681417367811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13995471739562454278245207 20993207609343681417367811)
        ·
          refine ⟨31489811414015522126051717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20993207609343681417367811 31489811414015522126051717)
          ·
            refine ⟨5904339640127910398634697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31489811414015522126051717 5904339640127910398634697)
            ·
              refine ⟨4428254730095932798976023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5904339640127910398634697 4428254730095932798976023)
              ·
                refine ⟨6642382095143899198464035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4428254730095932798976023 6642382095143899198464035)
                ·
                  refine ⟨9963573142715848797696053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6642382095143899198464035 9963573142715848797696053)
                  ·
                    refine ⟨934084982129610824784005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9963573142715848797696053 934084982129610824784005)
                    ·
                      rfl

theorem cell22_2728686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_2728686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728686 prefixEnd_2728686 := by exact prefixLift 2728686
  have htrace : WordTrace (prefixWord ++ tailWord_2728686) baseStart_2728686 baseEnd_2728686 := by
    simpa [prefixWord, tailWord_2728686, baseEnd_2728686] using wordTrace_append hprefix tailTrace_2728686
  have hstable : (prefixWord ++ tailWord_2728686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728686).length < 2 ^ (prefixWord ++ tailWord_2728686).sum := by decide
  have hdescent : baseEnd_2728686 < baseStart_2728686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728808 : List Nat := [2, 1, 4, 2, 1, 2, 3, 2, 1, 4]
def baseStart_2728808 : Nat := 118140960795 + 2728808 * 2 ^ 59
def prefixEnd_2728808 : Nat := 4983230072969 + 3 ^ 40 * 2728808 * 2
def baseEnd_2728808 : Nat := 934126745222843173233631

theorem tailTrace_2728808 : CollatzResearch.WordTrace tailWord_2728808 prefixEnd_2728808 934126745222843173233631 := by
  unfold tailWord_2728808
  simp only [CollatzResearch.WordTrace]
  refine ⟨49763902149001067073953539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66351869532001422765271385 49763902149001067073953539)
  ·
    refine ⟨74645853223501600610930309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49763902149001067073953539 74645853223501600610930309)
    ·
      refine ⟨13996097479406550114549433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74645853223501600610930309 13996097479406550114549433)
      ·
        refine ⟨10497073109554912585912075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13996097479406550114549433 10497073109554912585912075)
        ·
          refine ⟨15745609664332368878868113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10497073109554912585912075 15745609664332368878868113)
          ·
            refine ⟨11809207248249276659151085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15745609664332368878868113 11809207248249276659151085)
            ·
              refine ⟨4428452718093478747181657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11809207248249276659151085 4428452718093478747181657)
              ·
                refine ⟨3321339538570109060386243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4428452718093478747181657 3321339538570109060386243)
                ·
                  refine ⟨4982009307855163590579365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3321339538570109060386243 4982009307855163590579365)
                  ·
                    refine ⟨934126745222843173233631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4982009307855163590579365 934126745222843173233631)
                    ·
                      rfl

theorem cell22_2728808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_2728808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728808 prefixEnd_2728808 := by exact prefixLift 2728808
  have htrace : WordTrace (prefixWord ++ tailWord_2728808) baseStart_2728808 baseEnd_2728808 := by
    simpa [prefixWord, tailWord_2728808, baseEnd_2728808] using wordTrace_append hprefix tailTrace_2728808
  have hstable : (prefixWord ++ tailWord_2728808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728808).length < 2 ^ (prefixWord ++ tailWord_2728808).sum := by decide
  have hdescent : baseEnd_2728808 < baseStart_2728808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728819 : List Nat := [1, 1, 1, 2, 2, 1, 4, 3, 1, 6]
def baseStart_2728819 : Nat := 118140960795 + 2728819 * 2 ^ 59
def prefixEnd_2728819 : Nat := 4983230072969 + 3 ^ 40 * 2728819 * 2
def baseEnd_2728819 : Nat := 934130510747642811208597

theorem tailTrace_2728819 : CollatzResearch.WordTrace tailWord_2728819 prefixEnd_2728819 934130510747642811208597 := by
  unfold tailWord_2728819
  simp only [CollatzResearch.WordTrace]
  refine ⟨99528205500962283026557511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66352137000641522017705007 99528205500962283026557511)
  ·
    refine ⟨149292308251443424539836267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99528205500962283026557511 149292308251443424539836267)
    ·
      refine ⟨223938462377165136809754401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149292308251443424539836267 223938462377165136809754401)
      ·
        refine ⟨167953846782873852607315801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223938462377165136809754401 167953846782873852607315801)
        ·
          refine ⟨125965385087155389455486851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167953846782873852607315801 125965385087155389455486851)
          ·
            refine ⟨188948077630733084183230277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125965385087155389455486851 188948077630733084183230277)
            ·
              refine ⟨35427764555762453284355677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 188948077630733084183230277 35427764555762453284355677)
              ·
                refine ⟨13285411708410919981633379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35427764555762453284355677 13285411708410919981633379)
                ·
                  refine ⟨19928117562616379972450069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13285411708410919981633379 19928117562616379972450069)
                  ·
                    refine ⟨934130510747642811208597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19928117562616379972450069 934130510747642811208597)
                    ·
                      rfl

theorem cell22_2728819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 6].length) (baseStart_2728819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728819 prefixEnd_2728819 := by exact prefixLift 2728819
  have htrace : WordTrace (prefixWord ++ tailWord_2728819) baseStart_2728819 baseEnd_2728819 := by
    simpa [prefixWord, tailWord_2728819, baseEnd_2728819] using wordTrace_append hprefix tailTrace_2728819
  have hstable : (prefixWord ++ tailWord_2728819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728819).length < 2 ^ (prefixWord ++ tailWord_2728819).sum := by decide
  have hdescent : baseEnd_2728819 < baseStart_2728819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728821 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 3, 5]
def baseStart_2728821 : Nat := 118140960795 + 2728821 * 2 ^ 59
def prefixEnd_2728821 : Nat := 4983230072969 + 3 ^ 40 * 2728821 * 2
def baseEnd_2728821 : Nat := 934131195388515472658591

theorem tailTrace_2728821 : CollatzResearch.WordTrace tailWord_2728821 prefixEnd_2728821 934131195388515472658591 := by
  unfold tailWord_2728821
  simp only [CollatzResearch.WordTrace]
  refine ⟨99528278446955037368130317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66352185631303358245420211 99528278446955037368130317)
  ·
    refine ⟨37323104417608139013048869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99528278446955037368130317 37323104417608139013048869)
    ·
      refine ⟨6998082078301526064946663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37323104417608139013048869 6998082078301526064946663)
      ·
        refine ⟨10497123117452289097419995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6998082078301526064946663 10497123117452289097419995)
        ·
          refine ⟨15745684676178433646129993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10497123117452289097419995 15745684676178433646129993)
          ·
            refine ⟨11809263507133825234597495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15745684676178433646129993 11809263507133825234597495)
            ·
              refine ⟨17713895260700737851896243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11809263507133825234597495 17713895260700737851896243)
              ·
                refine ⟨26570842891051106777844365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17713895260700737851896243 26570842891051106777844365)
                ·
                  refine ⟨9964066084144165041691637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26570842891051106777844365 9964066084144165041691637)
                  ·
                    refine ⟨934131195388515472658591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9964066084144165041691637 934131195388515472658591)
                    ·
                      rfl

theorem cell22_2728821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_2728821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728821 prefixEnd_2728821 := by exact prefixLift 2728821
  have htrace : WordTrace (prefixWord ++ tailWord_2728821) baseStart_2728821 baseEnd_2728821 := by
    simpa [prefixWord, tailWord_2728821, baseEnd_2728821] using wordTrace_append hprefix tailTrace_2728821
  have hstable : (prefixWord ++ tailWord_2728821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728821).length < 2 ^ (prefixWord ++ tailWord_2728821).sum := by decide
  have hdescent : baseEnd_2728821 < baseStart_2728821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728840 : List Nat := [2, 1, 3, 3, 2, 1, 4, 2, 4]
def baseStart_2728840 : Nat := 118140960795 + 2728840 * 2 ^ 59
def prefixEnd_2728840 : Nat := 4983230072969 + 3 ^ 40 * 2728840 * 2
def baseEnd_2728840 : Nat := 311379233158935252144511

theorem tailTrace_2728840 : CollatzResearch.WordTrace tailWord_2728840 prefixEnd_2728840 311379233158935252144511 := by
  unfold tailWord_2728840
  simp only [CollatzResearch.WordTrace]
  refine ⟨49764485716943101806535987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66352647622590802408714649 49764485716943101806535987)
  ·
    refine ⟨74646728575414652709803981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49764485716943101806535987 74646728575414652709803981)
    ·
      refine ⟨27992523215780494766176493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74646728575414652709803981 27992523215780494766176493)
      ·
        refine ⟨10497196205917685537316185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27992523215780494766176493 10497196205917685537316185)
        ·
          refine ⟨7872897154438264152987139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10497196205917685537316185 7872897154438264152987139)
          ·
            refine ⟨11809345731657396229480709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7872897154438264152987139 11809345731657396229480709)
            ·
              refine ⟨2214252324685761793027633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11809345731657396229480709 2214252324685761793027633)
              ·
                refine ⟨1660689243514321344770725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2214252324685761793027633 1660689243514321344770725)
                ·
                  refine ⟨311379233158935252144511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1660689243514321344770725 311379233158935252144511)
                  ·
                    rfl

theorem cell22_2728840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 2, 4].length) (baseStart_2728840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728840 prefixEnd_2728840 := by exact prefixLift 2728840
  have htrace : WordTrace (prefixWord ++ tailWord_2728840) baseStart_2728840 baseEnd_2728840 := by
    simpa [prefixWord, tailWord_2728840, baseEnd_2728840] using wordTrace_append hprefix tailTrace_2728840
  have hstable : (prefixWord ++ tailWord_2728840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728840).length < 2 ^ (prefixWord ++ tailWord_2728840).sum := by decide
  have hdescent : baseEnd_2728840 < baseStart_2728840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728849 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 2, 7]
def baseStart_2728849 : Nat := 118140960795 + 2728849 * 2 ^ 59
def prefixEnd_2728849 : Nat := 4983230072969 + 3 ^ 40 * 2728849 * 2
def baseEnd_2728849 : Nat := 934140780360732732958505

theorem tailTrace_2728849 : CollatzResearch.WordTrace tailWord_2728849 prefixEnd_2728849 934140780360732732958505 := by
  unfold tailWord_2728849
  simp only [CollatzResearch.WordTrace]
  refine ⟨99529299690853598150149601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66352866460569065433433067 99529299690853598150149601)
  ·
    refine ⟨74646974768140198612612201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99529299690853598150149601 74646974768140198612612201)
    ·
      refine ⟨55985231076105148959459151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74646974768140198612612201 55985231076105148959459151)
      ·
        refine ⟨83977846614157723439188727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55985231076105148959459151 83977846614157723439188727)
        ·
          refine ⟨125966769921236585158783091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83977846614157723439188727 125966769921236585158783091)
          ·
            refine ⟨188950154881854877738174637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125966769921236585158783091 188950154881854877738174637)
            ·
              refine ⟨70856308080695579151815489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 188950154881854877738174637 70856308080695579151815489)
              ·
                refine ⟨53142231060521684363861617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70856308080695579151815489 53142231060521684363861617)
                ·
                  refine ⟨39856673295391263272896213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53142231060521684363861617 39856673295391263272896213)
                  ·
                    refine ⟨934140780360732732958505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39856673295391263272896213 934140780360732732958505)
                    ·
                      rfl

theorem cell22_2728849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_2728849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728849 prefixEnd_2728849 := by exact prefixLift 2728849
  have htrace : WordTrace (prefixWord ++ tailWord_2728849) baseStart_2728849 baseEnd_2728849 := by
    simpa [prefixWord, tailWord_2728849, baseEnd_2728849] using wordTrace_append hprefix tailTrace_2728849
  have hstable : (prefixWord ++ tailWord_2728849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728849).length < 2 ^ (prefixWord ++ tailWord_2728849).sum := by decide
  have hdescent : baseEnd_2728849 < baseStart_2728849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728896 : List Nat := [2, 1, 1, 2, 3, 4, 1, 1, 7]
def baseStart_2728896 : Nat := 118140960795 + 2728896 * 2 ^ 59
def prefixEnd_2728896 : Nat := 4983230072969 + 3 ^ 40 * 2728896 * 2
def baseEnd_2728896 : Nat := 311385623140413425677787

theorem tailTrace_2728896 : CollatzResearch.WordTrace tailWord_2728896 prefixEnd_2728896 311385623140413425677787 := by
  unfold tailWord_2728896
  simp only [CollatzResearch.WordTrace]
  refine ⟨49765506960841662588555271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66354009281122216784740361 49765506960841662588555271)
  ·
    refine ⟨74648260441262493882832907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49765506960841662588555271 74648260441262493882832907)
    ·
      refine ⟨111972390661893740824249361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74648260441262493882832907 111972390661893740824249361)
      ·
        refine ⟨83979292996420305618187021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111972390661893740824249361 83979292996420305618187021)
        ·
          refine ⟨31492234873657614606820133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83979292996420305618187021 31492234873657614606820133)
          ·
            refine ⟨5904794038810802738778775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31492234873657614606820133 5904794038810802738778775)
            ·
              refine ⟨8857191058216204108168163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5904794038810802738778775 8857191058216204108168163)
              ·
                refine ⟨13285786587324306162252245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8857191058216204108168163 13285786587324306162252245)
                ·
                  refine ⟨311385623140413425677787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13285786587324306162252245 311385623140413425677787)
                  ·
                    rfl

theorem cell22_2728896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 7].length) (baseStart_2728896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728896 prefixEnd_2728896 := by exact prefixLift 2728896
  have htrace : WordTrace (prefixWord ++ tailWord_2728896) baseStart_2728896 baseEnd_2728896 := by
    simpa [prefixWord, tailWord_2728896, baseEnd_2728896] using wordTrace_append hprefix tailTrace_2728896
  have hstable : (prefixWord ++ tailWord_2728896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728896).length < 2 ^ (prefixWord ++ tailWord_2728896).sum := by decide
  have hdescent : baseEnd_2728896 < baseStart_2728896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728911 : List Nat := [1, 1, 2, 1, 1, 6, 2, 1, 2, 5]
def baseStart_2728911 : Nat := 118140960795 + 2728911 * 2 ^ 59
def prefixEnd_2728911 : Nat := 4983230072969 + 3 ^ 40 * 2728911 * 2
def baseEnd_2728911 : Nat := 934162004227785237908315

theorem tailTrace_2728911 : CollatzResearch.WordTrace tailWord_2728911 prefixEnd_2728911 934162004227785237908315 := by
  unfold tailWord_2728911
  simp only [CollatzResearch.WordTrace]
  refine ⟨99531561016628982738906587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66354374011085988492604391 99531561016628982738906587)
  ·
    refine ⟨149297341524943474108359881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99531561016628982738906587 149297341524943474108359881)
    ·
      refine ⟨111973006143707605581269911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149297341524943474108359881 111973006143707605581269911)
      ·
        refine ⟨167959509215561408371904867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111973006143707605581269911 167959509215561408371904867)
        ·
          refine ⟨251939263823342112557857301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167959509215561408371904867 251939263823342112557857301)
          ·
            refine ⟨11809652991719161526149561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 251939263823342112557857301 11809652991719161526149561)
            ·
              refine ⟨8857239743789371144612171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11809652991719161526149561 8857239743789371144612171)
              ·
                refine ⟨13285859615684056716918257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8857239743789371144612171 13285859615684056716918257)
                ·
                  refine ⟨9964394711763042537688693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13285859615684056716918257 9964394711763042537688693)
                  ·
                    refine ⟨934162004227785237908315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9964394711763042537688693 934162004227785237908315)
                    ·
                      rfl

theorem cell22_2728911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 5].length) (baseStart_2728911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728911 prefixEnd_2728911 := by exact prefixLift 2728911
  have htrace : WordTrace (prefixWord ++ tailWord_2728911) baseStart_2728911 baseEnd_2728911 := by
    simpa [prefixWord, tailWord_2728911, baseEnd_2728911] using wordTrace_append hprefix tailTrace_2728911
  have hstable : (prefixWord ++ tailWord_2728911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728911).length < 2 ^ (prefixWord ++ tailWord_2728911).sum := by decide
  have hdescent : baseEnd_2728911 < baseStart_2728911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728913 : List Nat := [1, 2, 2, 1, 2, 1, 7, 1, 5]
def baseStart_2728913 : Nat := 118140960795 + 2728913 * 2 ^ 59
def prefixEnd_2728913 : Nat := 4983230072969 + 3 ^ 40 * 2728913 * 2
def baseEnd_2728913 : Nat := 311387562956219299786103

theorem tailTrace_2728913 : CollatzResearch.WordTrace tailWord_2728913 prefixEnd_2728913 311387562956219299786103 := by
  unfold tailWord_2728913
  simp only [CollatzResearch.WordTrace]
  refine ⟨99531633962621737080479393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66354422641747824720319595 99531633962621737080479393)
  ·
    refine ⟨74648725471966302810359545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99531633962621737080479393 74648725471966302810359545)
    ·
      refine ⟨55986544103974727107769659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74648725471966302810359545 55986544103974727107769659)
      ·
        refine ⟨83979816155962090661654489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55986544103974727107769659 83979816155962090661654489)
        ·
          refine ⟨62984862116971567996240867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83979816155962090661654489 62984862116971567996240867)
          ·
            refine ⟨94477293175457351994361301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62984862116971567996240867 94477293175457351994361301)
            ·
              refine ⟨2214311558799781687367843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 94477293175457351994361301 2214311558799781687367843)
              ·
                refine ⟨3321467338199672531051765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2214311558799781687367843 3321467338199672531051765)
                ·
                  refine ⟨311387562956219299786103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3321467338199672531051765 311387562956219299786103)
                  ·
                    rfl

theorem cell22_2728913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 5].length) (baseStart_2728913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728913 prefixEnd_2728913 := by exact prefixLift 2728913
  have htrace : WordTrace (prefixWord ++ tailWord_2728913) baseStart_2728913 baseEnd_2728913 := by
    simpa [prefixWord, tailWord_2728913, baseEnd_2728913] using wordTrace_append hprefix tailTrace_2728913
  have hstable : (prefixWord ++ tailWord_2728913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728913).length < 2 ^ (prefixWord ++ tailWord_2728913).sum := by decide
  have hdescent : baseEnd_2728913 < baseStart_2728913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728943 : List Nat := [1, 1, 2, 1, 4, 3, 2, 3, 1, 4]
def baseStart_2728943 : Nat := 118140960795 + 2728943 * 2 ^ 59
def prefixEnd_2728943 : Nat := 4983230072969 + 3 ^ 40 * 2728943 * 2
def baseEnd_2728943 : Nat := 934172958481747821108217

theorem tailTrace_2728943 : CollatzResearch.WordTrace tailWord_2728943 prefixEnd_2728943 934172958481747821108217 := by
  unfold tailWord_2728943
  simp only [CollatzResearch.WordTrace]
  refine ⟨99532728152513052204071483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66355152101675368136047655 99532728152513052204071483)
  ·
    refine ⟨149299092228769578306107225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99532728152513052204071483 149299092228769578306107225)
    ·
      refine ⟨111974319171577183729580419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149299092228769578306107225 111974319171577183729580419)
      ·
        refine ⟨167961478757365775594370629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111974319171577183729580419 167961478757365775594370629)
        ·
          refine ⟨31492777267006082923944493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167961478757365775594370629 31492777267006082923944493)
          ·
            refine ⟨11809791475127281096479185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31492777267006082923944493 11809791475127281096479185)
            ·
              refine ⟨8857343606345460822359389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11809791475127281096479185 8857343606345460822359389)
              ·
                refine ⟨3321503852379547808384771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8857343606345460822359389 3321503852379547808384771)
                ·
                  refine ⟨4982255778569321712577157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3321503852379547808384771 4982255778569321712577157)
                  ·
                    refine ⟨934172958481747821108217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4982255778569321712577157 934172958481747821108217)
                    ·
                      rfl

theorem cell22_2728943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 4].length) (baseStart_2728943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728943 prefixEnd_2728943 := by exact prefixLift 2728943
  have htrace : WordTrace (prefixWord ++ tailWord_2728943) baseStart_2728943 baseEnd_2728943 := by
    simpa [prefixWord, tailWord_2728943, baseEnd_2728943] using wordTrace_append hprefix tailTrace_2728943
  have hstable : (prefixWord ++ tailWord_2728943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728943).length < 2 ^ (prefixWord ++ tailWord_2728943).sum := by decide
  have hdescent : baseEnd_2728943 < baseStart_2728943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2728986 : List Nat := [3, 1, 1, 3, 1, 2, 1, 10]
def baseStart_2728986 : Nat := 118140960795 + 2728986 * 2 ^ 59
def prefixEnd_2728986 : Nat := 4983230072969 + 3 ^ 40 * 2728986 * 2
def baseEnd_2728986 : Nat := 103798630917834449142565

theorem tailTrace_2728986 : CollatzResearch.WordTrace tailWord_2728986 prefixEnd_2728986 103798630917834449142565 := by
  unfold tailWord_2728986
  simp only [CollatzResearch.WordTrace]
  refine ⟨24883574122839317636971703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66356197660904847031924541 24883574122839317636971703)
  ·
    refine ⟨37325361184258976455457555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24883574122839317636971703 37325361184258976455457555)
    ·
      refine ⟨55988041776388464683186333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37325361184258976455457555 55988041776388464683186333)
      ·
        refine ⟨20995515666145674256194875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55988041776388464683186333 20995515666145674256194875)
        ·
          refine ⟨31493273499218511384292313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20995515666145674256194875 31493273499218511384292313)
          ·
            refine ⟨23619955124413883538219235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31493273499218511384292313 23619955124413883538219235)
            ·
              refine ⟨35429932686620825307328853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23619955124413883538219235 35429932686620825307328853)
              ·
                refine ⟨103798630917834449142565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35429932686620825307328853 103798630917834449142565)
                ·
                  rfl

theorem cell22_2728986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 10].length) (baseStart_2728986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2728986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2728986 prefixEnd_2728986 := by exact prefixLift 2728986
  have htrace : WordTrace (prefixWord ++ tailWord_2728986) baseStart_2728986 baseEnd_2728986 := by
    simpa [prefixWord, tailWord_2728986, baseEnd_2728986] using wordTrace_append hprefix tailTrace_2728986
  have hstable : (prefixWord ++ tailWord_2728986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2728986).length < 2 ^ (prefixWord ++ tailWord_2728986).sum := by decide
  have hdescent : baseEnd_2728986 < baseStart_2728986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2728986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729063 : List Nat := [1, 1, 5, 1, 1, 3, 1, 2, 2, 5]
def baseStart_2729063 : Nat := 118140960795 + 2729063 * 2 ^ 59
def prefixEnd_2729063 : Nat := 4983230072969 + 3 ^ 40 * 2729063 * 2
def baseEnd_2729063 : Nat := 934214036934107508107849

theorem tailTrace_2729063 : CollatzResearch.WordTrace tailWord_2729063 prefixEnd_2729063 934214036934107508107849 := by
  unfold tailWord_2729063
  simp only [CollatzResearch.WordTrace]
  refine ⟨99537104912078312698439843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66358069941385541798959895 99537104912078312698439843)
  ·
    refine ⟨149305657368117469047659765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99537104912078312698439843 149305657368117469047659765)
    ·
      refine ⟨13997405378261012723218103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 149305657368117469047659765 13997405378261012723218103)
      ·
        refine ⟨20996108067391519084827155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13997405378261012723218103 20996108067391519084827155)
        ·
          refine ⟨31494162101087278627240733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20996108067391519084827155 31494162101087278627240733)
          ·
            refine ⟨11810310787907729485215275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31494162101087278627240733 11810310787907729485215275)
            ·
              refine ⟨17715466181861594227822913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11810310787907729485215275 17715466181861594227822913)
              ·
                refine ⟨13286599636396195670867185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17715466181861594227822913 13286599636396195670867185)
                ·
                  refine ⟨9964949727297146753150389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13286599636396195670867185 9964949727297146753150389)
                  ·
                    refine ⟨934214036934107508107849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9964949727297146753150389 934214036934107508107849)
                    ·
                      rfl

theorem cell22_2729063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_2729063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729063 prefixEnd_2729063 := by exact prefixLift 2729063
  have htrace : WordTrace (prefixWord ++ tailWord_2729063) baseStart_2729063 baseEnd_2729063 := by
    simpa [prefixWord, tailWord_2729063, baseEnd_2729063] using wordTrace_append hprefix tailTrace_2729063
  have hstable : (prefixWord ++ tailWord_2729063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729063).length < 2 ^ (prefixWord ++ tailWord_2729063).sum := by decide
  have hdescent : baseEnd_2729063 < baseStart_2729063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729065 : List Nat := [1, 2, 1, 1, 1, 8, 1, 2, 5]
def baseStart_2729065 : Nat := 118140960795 + 2729065 * 2 ^ 59
def prefixEnd_2729065 : Nat := 4983230072969 + 3 ^ 40 * 2729065 * 2
def baseEnd_2729065 : Nat := 311404907191660056519281

theorem tailTrace_2729065 : CollatzResearch.WordTrace tailWord_2729065 prefixEnd_2729065 311404907191660056519281 := by
  unfold tailWord_2729065
  simp only [CollatzResearch.WordTrace]
  refine ⟨99537177858071067040012649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66358118572047378026675099 99537177858071067040012649)
  ·
    refine ⟨74652883393553300280009487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99537177858071067040012649 74652883393553300280009487)
    ·
      refine ⟨111979325090329950420014231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74652883393553300280009487 111979325090329950420014231)
      ·
        refine ⟨167968987635494925630021347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111979325090329950420014231 167968987635494925630021347)
        ·
          refine ⟨251953481453242388445032021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167968987635494925630021347 251953481453242388445032021)
          ·
            refine ⟨2952579860780184239590219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 251953481453242388445032021 2952579860780184239590219)
            ·
              refine ⟨4428869791170276359385329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2952579860780184239590219 4428869791170276359385329)
              ·
                refine ⟨3321652343377707269538997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4428869791170276359385329 3321652343377707269538997)
                ·
                  refine ⟨311404907191660056519281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3321652343377707269538997 311404907191660056519281)
                  ·
                    rfl

theorem cell22_2729065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 5].length) (baseStart_2729065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729065 prefixEnd_2729065 := by exact prefixLift 2729065
  have htrace : WordTrace (prefixWord ++ tailWord_2729065) baseStart_2729065 baseEnd_2729065 := by
    simpa [prefixWord, tailWord_2729065, baseEnd_2729065] using wordTrace_append hprefix tailTrace_2729065
  have hstable : (prefixWord ++ tailWord_2729065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729065).length < 2 ^ (prefixWord ++ tailWord_2729065).sum := by decide
  have hdescent : baseEnd_2729065 < baseStart_2729065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729125 : List Nat := [1, 3, 1, 2, 1, 4, 2, 1, 4, 3]
def baseStart_2729125 : Nat := 118140960795 + 2729125 * 2 ^ 59
def prefixEnd_2729125 : Nat := 4983230072969 + 3 ^ 40 * 2729125 * 2
def baseEnd_2729125 : Nat := 934235260801160013057659

theorem tailTrace_2729125 : CollatzResearch.WordTrace tailWord_2729125 prefixEnd_2729125 934235260801160013057659 := by
  unfold tailWord_2729125
  simp only [CollatzResearch.WordTrace]
  refine ⟨99539366237853697287196829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66359577491902464858131219 99539366237853697287196829)
  ·
    refine ⟨37327262339195136482698811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99539366237853697287196829 37327262339195136482698811)
    ·
      refine ⟨55990893508792704724048217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37327262339195136482698811 55990893508792704724048217)
      ·
        refine ⟨41993170131594528543036163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55990893508792704724048217 41993170131594528543036163)
        ·
          refine ⟨62989755197391792814554245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41993170131594528543036163 62989755197391792814554245)
          ·
            refine ⟨11810579099510961152728921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62989755197391792814554245 11810579099510961152728921)
            ·
              refine ⟨8857934324633220864546691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11810579099510961152728921 8857934324633220864546691)
              ·
                refine ⟨13286901486949831296820037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8857934324633220864546691 13286901486949831296820037)
                ·
                  refine ⟨2491294028803093368153757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13286901486949831296820037 2491294028803093368153757)
                  ·
                    refine ⟨934235260801160013057659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2491294028803093368153757 934235260801160013057659)
                    ·
                      rfl

theorem cell22_2729125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 4, 3].length) (baseStart_2729125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729125 prefixEnd_2729125 := by exact prefixLift 2729125
  have htrace : WordTrace (prefixWord ++ tailWord_2729125) baseStart_2729125 baseEnd_2729125 := by
    simpa [prefixWord, tailWord_2729125, baseEnd_2729125] using wordTrace_append hprefix tailTrace_2729125
  have hstable : (prefixWord ++ tailWord_2729125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729125).length < 2 ^ (prefixWord ++ tailWord_2729125).sum := by decide
  have hdescent : baseEnd_2729125 < baseStart_2729125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729127 : List Nat := [1, 1, 6, 2, 1, 3, 1, 1, 6]
def baseStart_2729127 : Nat := 118140960795 + 2729127 * 2 ^ 59
def prefixEnd_2729127 : Nat := 4983230072969 + 3 ^ 40 * 2729127 * 2
def baseEnd_2729127 : Nat := 311411981814010891502551

theorem tailTrace_2729127 : CollatzResearch.WordTrace tailWord_2729127 prefixEnd_2729127 311411981814010891502551 := by
  unfold tailWord_2729127
  simp only [CollatzResearch.WordTrace]
  refine ⟨99539439183846451628769635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66359626122564301085846423 99539439183846451628769635)
  ·
    refine ⟨149309158775769677443154453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99539439183846451628769635 149309158775769677443154453)
    ·
      refine ⟨6998866817614203630147865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 149309158775769677443154453 6998866817614203630147865)
      ·
        refine ⟨5249150113210652722610899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6998866817614203630147865 5249150113210652722610899)
        ·
          refine ⟨7873725169815979083916349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5249150113210652722610899 7873725169815979083916349)
          ·
            refine ⟨2952646938680992156468631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7873725169815979083916349 2952646938680992156468631)
            ·
              refine ⟨4428970408021488234702947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2952646938680992156468631 4428970408021488234702947)
              ·
                refine ⟨6643455612032232352054421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4428970408021488234702947 6643455612032232352054421)
                ·
                  refine ⟨311411981814010891502551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6643455612032232352054421 311411981814010891502551)
                  ·
                    rfl

theorem cell22_2729127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 6].length) (baseStart_2729127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729127 prefixEnd_2729127 := by exact prefixLift 2729127
  have htrace : WordTrace (prefixWord ++ tailWord_2729127) baseStart_2729127 baseEnd_2729127 := by
    simpa [prefixWord, tailWord_2729127, baseEnd_2729127] using wordTrace_append hprefix tailTrace_2729127
  have hstable : (prefixWord ++ tailWord_2729127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729127).length < 2 ^ (prefixWord ++ tailWord_2729127).sum := by decide
  have hdescent : baseEnd_2729127 < baseStart_2729127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729138 : List Nat := [3, 2, 1, 1, 1, 4, 1, 9]
def baseStart_2729138 : Nat := 118140960795 + 2729138 * 2 ^ 59
def prefixEnd_2729138 : Nat := 4983230072969 + 3 ^ 40 * 2729138 * 2
def baseEnd_2729138 : Nat := 103804412329648034720291

theorem tailTrace_2729138 : CollatzResearch.WordTrace tailWord_2729138 prefixEnd_2729138 103804412329648034720291 := by
  unfold tailWord_2729138
  simp only [CollatzResearch.WordTrace]
  refine ⟨24884960096701650126855017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66359893591204400338280045 24884960096701650126855017)
  ·
    refine ⟨18663720072526237595141263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24884960096701650126855017 18663720072526237595141263)
    ·
      refine ⟨27995580108789356392711895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18663720072526237595141263 27995580108789356392711895)
      ·
        refine ⟨41993370163184034589067843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27995580108789356392711895 41993370163184034589067843)
        ·
          refine ⟨62990055244776051883601765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41993370163184034589067843 62990055244776051883601765)
          ·
            refine ⟨11810635358395509728175331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62990055244776051883601765 11810635358395509728175331)
            ·
              refine ⟨17715953037593264592262997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11810635358395509728175331 17715953037593264592262997)
              ·
                refine ⟨103804412329648034720291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17715953037593264592262997 103804412329648034720291)
                ·
                  rfl

theorem cell22_2729138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 9].length) (baseStart_2729138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729138 prefixEnd_2729138 := by exact prefixLift 2729138
  have htrace : WordTrace (prefixWord ++ tailWord_2729138) baseStart_2729138 baseEnd_2729138 := by
    simpa [prefixWord, tailWord_2729138, baseEnd_2729138] using wordTrace_append hprefix tailTrace_2729138
  have hstable : (prefixWord ++ tailWord_2729138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729138).length < 2 ^ (prefixWord ++ tailWord_2729138).sum := by decide
  have hdescent : baseEnd_2729138 < baseStart_2729138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729172 : List Nat := [2, 4, 1, 4, 2, 9]
def baseStart_2729172 : Nat := 118140960795 + 2729172 * 2 ^ 59
def prefixEnd_2729172 : Nat := 4983230072969 + 3 ^ 40 * 2729172 * 2
def baseEnd_2729172 : Nat := 11533967282242809347315

theorem tailTrace_2729172 : CollatzResearch.WordTrace tailWord_2729172 prefixEnd_2729172 11533967282242809347315 := by
  unfold tailWord_2729172
  simp only [CollatzResearch.WordTrace]
  refine ⟨49770540234341712157078885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66360720312455616209438513 49770540234341712157078885)
  ·
    refine ⟨9331976293939071029452291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49770540234341712157078885 9331976293939071029452291)
    ·
      refine ⟨13997964440908606544178437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9331976293939071029452291 13997964440908606544178437)
      ·
        refine ⟨2624618332670363727033457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13997964440908606544178437 2624618332670363727033457)
        ·
          refine ⟨1968463749502772795275093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2624618332670363727033457 1968463749502772795275093)
          ·
            refine ⟨11533967282242809347315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1968463749502772795275093 11533967282242809347315)
            ·
              rfl

theorem cell22_2729172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 9].length) (baseStart_2729172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729172 prefixEnd_2729172 := by exact prefixLift 2729172
  have htrace : WordTrace (prefixWord ++ tailWord_2729172) baseStart_2729172 baseEnd_2729172 := by
    simpa [prefixWord, tailWord_2729172, baseEnd_2729172] using wordTrace_append hprefix tailTrace_2729172
  have hstable : (prefixWord ++ tailWord_2729172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729172).length < 2 ^ (prefixWord ++ tailWord_2729172).sum := by decide
  have hdescent : baseEnd_2729172 < baseStart_2729172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729183 : List Nat := [1, 1, 2, 3, 2, 1, 2, 3, 7]
def baseStart_2729183 : Nat := 118140960795 + 2729183 * 2 ^ 59
def prefixEnd_2729183 : Nat := 4983230072969 + 3 ^ 40 * 2729183 * 2
def baseEnd_2729183 : Nat := 311418371795489065035827

theorem tailTrace_2729183 : CollatzResearch.WordTrace tailWord_2729183 prefixEnd_2729183 311418371795489065035827 := by
  unfold tailWord_2729183
  simp only [CollatzResearch.WordTrace]
  refine ⟨99541481671643573192808203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66360987781095715461872135 99541481671643573192808203)
  ·
    refine ⟨149312222507465359789212305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99541481671643573192808203 149312222507465359789212305)
    ·
      refine ⟨111984166880599019841909229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149312222507465359789212305 111984166880599019841909229)
      ·
        refine ⟨41994062580224632440715961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111984166880599019841909229 41994062580224632440715961)
        ·
          refine ⟨31495546935168474330536971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41994062580224632440715961 31495546935168474330536971)
          ·
            refine ⟨47243320402752711495805457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31495546935168474330536971 47243320402752711495805457)
            ·
              refine ⟨35432490302064533621854093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47243320402752711495805457 35432490302064533621854093)
              ·
                refine ⟨13287183863274200108195285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35432490302064533621854093 13287183863274200108195285)
                ·
                  refine ⟨311418371795489065035827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13287183863274200108195285 311418371795489065035827)
                  ·
                    rfl

theorem cell22_2729183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 7].length) (baseStart_2729183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729183 prefixEnd_2729183 := by exact prefixLift 2729183
  have htrace : WordTrace (prefixWord ++ tailWord_2729183) baseStart_2729183 baseEnd_2729183 := by
    simpa [prefixWord, tailWord_2729183, baseEnd_2729183] using wordTrace_append hprefix tailTrace_2729183
  have hstable : (prefixWord ++ tailWord_2729183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729183).length < 2 ^ (prefixWord ++ tailWord_2729183).sum := by decide
  have hdescent : baseEnd_2729183 < baseStart_2729183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729234 : List Nat := [3, 2, 4, 2, 1, 1, 1, 1, 7]
def baseStart_2729234 : Nat := 118140960795 + 2729234 * 2 ^ 59
def prefixEnd_2729234 : Nat := 4983230072969 + 3 ^ 40 * 2729234 * 2
def baseEnd_2729234 : Nat := 311424191242906687360775

theorem tailTrace_2729234 : CollatzResearch.WordTrace tailWord_2729234 prefixEnd_2729234 311424191242906687360775 := by
  unfold tailWord_2729234
  simp only [CollatzResearch.WordTrace]
  refine ⟨24885835448614702225728689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66362227862972539268609837 24885835448614702225728689)
  ·
    refine ⟨18664376586461026669296517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24885835448614702225728689 18664376586461026669296517)
    ·
      refine ⟨3499570609961442500493097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18664376586461026669296517 3499570609961442500493097)
      ·
        refine ⟨2624677957471081875369823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3499570609961442500493097 2624677957471081875369823)
        ·
          refine ⟨3937016936206622813054735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2624677957471081875369823 3937016936206622813054735)
          ·
            refine ⟨5905525404309934219582103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3937016936206622813054735 5905525404309934219582103)
            ·
              refine ⟨8858288106464901329373155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5905525404309934219582103 8858288106464901329373155)
              ·
                refine ⟨13287432159697351994059733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8858288106464901329373155 13287432159697351994059733)
                ·
                  refine ⟨311424191242906687360775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13287432159697351994059733 311424191242906687360775)
                  ·
                    rfl

theorem cell22_2729234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_2729234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729234 prefixEnd_2729234 := by exact prefixLift 2729234
  have htrace : WordTrace (prefixWord ++ tailWord_2729234) baseStart_2729234 baseEnd_2729234 := by
    simpa [prefixWord, tailWord_2729234, baseEnd_2729234] using wordTrace_append hprefix tailTrace_2729234
  have hstable : (prefixWord ++ tailWord_2729234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729234).length < 2 ^ (prefixWord ++ tailWord_2729234).sum := by decide
  have hdescent : baseEnd_2729234 < baseStart_2729234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729279 : List Nat := [1, 1, 2, 2, 4, 4, 1, 3, 4]
def baseStart_2729279 : Nat := 118140960795 + 2729279 * 2 ^ 59
def prefixEnd_2729279 : Nat := 4983230072969 + 3 ^ 40 * 2729279 * 2
def baseEnd_2729279 : Nat := 311429326049451648235729

theorem tailTrace_2729279 : CollatzResearch.WordTrace tailWord_2729279 prefixEnd_2729279 311429326049451648235729 := by
  unfold tailWord_2729279
  simp only [CollatzResearch.WordTrace]
  refine ⟨99544983079295781588302891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66363322052863854392201927 99544983079295781588302891)
  ·
    refine ⟨149317474618943672382454337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99544983079295781588302891 149317474618943672382454337)
    ·
      refine ⟨111988105964207754286840753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149317474618943672382454337 111988105964207754286840753)
      ·
        refine ⟨83991079473155815715130565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111988105964207754286840753 83991079473155815715130565)
        ·
          refine ⟨15748327401216715446586981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83991079473155815715130565 15748327401216715446586981)
          ·
            refine ⟨2952811387728134146235059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15748327401216715446586981 2952811387728134146235059)
            ·
              refine ⟨4429217081592201219352589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2952811387728134146235059 4429217081592201219352589)
              ·
                refine ⟨1660956405597075457257221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4429217081592201219352589 1660956405597075457257221)
                ·
                  refine ⟨311429326049451648235729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1660956405597075457257221 311429326049451648235729)
                  ·
                    rfl

theorem cell22_2729279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 3, 4].length) (baseStart_2729279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729279 prefixEnd_2729279 := by exact prefixLift 2729279
  have htrace : WordTrace (prefixWord ++ tailWord_2729279) baseStart_2729279 baseEnd_2729279 := by
    simpa [prefixWord, tailWord_2729279, baseEnd_2729279] using wordTrace_append hprefix tailTrace_2729279
  have hstable : (prefixWord ++ tailWord_2729279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729279).length < 2 ^ (prefixWord ++ tailWord_2729279).sum := by decide
  have hdescent : baseEnd_2729279 < baseStart_2729279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729292 : List Nat := [2, 2, 1, 3, 2, 3, 1, 2, 2, 4]
def baseStart_2729292 : Nat := 118140960795 + 2729292 * 2 ^ 59
def prefixEnd_2729292 : Nat := 4983230072969 + 3 ^ 40 * 2729292 * 2
def baseEnd_2729292 : Nat := 934292428314027244132147

theorem tailTrace_2729292 : CollatzResearch.WordTrace tailWord_2729292 prefixEnd_2729292 934292428314027244132147 := by
  unfold tailWord_2729292
  simp only [CollatzResearch.WordTrace]
  refine ⟨49772728614124342404263065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66363638152165789872350753 49772728614124342404263065)
  ·
    refine ⟨37329546460593256803197299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49772728614124342404263065 37329546460593256803197299)
    ·
      refine ⟨55994319690889885204795949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37329546460593256803197299 55994319690889885204795949)
      ·
        refine ⟨20997869884083706951798481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55994319690889885204795949 20997869884083706951798481)
        ·
          refine ⟨15748402413062780213848861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20997869884083706951798481 15748402413062780213848861)
          ·
            refine ⟨5905650904898542580193323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15748402413062780213848861 5905650904898542580193323)
            ·
              refine ⟨8858476357347813870289985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5905650904898542580193323 8858476357347813870289985)
              ·
                refine ⟨6643857268010860402717489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8858476357347813870289985 6643857268010860402717489)
                ·
                  refine ⟨4982892951008145302038117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6643857268010860402717489 4982892951008145302038117)
                  ·
                    refine ⟨934292428314027244132147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4982892951008145302038117 934292428314027244132147)
                    ·
                      rfl

theorem cell22_2729292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_2729292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729292 prefixEnd_2729292 := by exact prefixLift 2729292
  have htrace : WordTrace (prefixWord ++ tailWord_2729292) baseStart_2729292 baseEnd_2729292 := by
    simpa [prefixWord, tailWord_2729292, baseEnd_2729292] using wordTrace_append hprefix tailTrace_2729292
  have hstable : (prefixWord ++ tailWord_2729292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729292).length < 2 ^ (prefixWord ++ tailWord_2729292).sum := by decide
  have hdescent : baseEnd_2729292 < baseStart_2729292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729302 : List Nat := [5, 2, 3, 1, 2, 1, 2, 1, 5]
def baseStart_2729302 : Nat := 118140960795 + 2729302 * 2 ^ 59
def prefixEnd_2729302 : Nat := 4983230072969 + 3 ^ 40 * 2729302 * 2
def baseEnd_2729302 : Nat := 311431950506130183794039

theorem tailTrace_2729302 : CollatzResearch.WordTrace tailWord_2729302 prefixEnd_2729302 311431950506130183794039 := by
  unfold tailWord_2729302
  simp only [CollatzResearch.WordTrace]
  refine ⟨6221613872388278532274385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66363881305474971010926773 6221613872388278532274385)
  ·
    refine ⟨4666210404291208899205789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6221613872388278532274385 4666210404291208899205789)
    ·
      refine ⟨1749828901609203337202171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4666210404291208899205789 1749828901609203337202171)
      ·
        refine ⟨2624743352413805005803257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1749828901609203337202171 2624743352413805005803257)
        ·
          refine ⟨1968557514310353754352443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2624743352413805005803257 1968557514310353754352443)
          ·
            refine ⟨2952836271465530631528665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1968557514310353754352443 2952836271465530631528665)
            ·
              refine ⟨2214627203599147973646499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2952836271465530631528665 2214627203599147973646499)
              ·
                refine ⟨3321940805398721960469749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2214627203599147973646499 3321940805398721960469749)
                ·
                  refine ⟨311431950506130183794039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3321940805398721960469749 311431950506130183794039)
                  ·
                    rfl

theorem cell22_2729302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_2729302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729302 prefixEnd_2729302 := by exact prefixLift 2729302
  have htrace : WordTrace (prefixWord ++ tailWord_2729302) baseStart_2729302 baseEnd_2729302 := by
    simpa [prefixWord, tailWord_2729302, baseEnd_2729302] using wordTrace_append hprefix tailTrace_2729302
  have hstable : (prefixWord ++ tailWord_2729302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729302).length < 2 ^ (prefixWord ++ tailWord_2729302).sum := by decide
  have hdescent : baseEnd_2729302 < baseStart_2729302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729326 : List Nat := [4, 1, 2, 4, 1, 1, 2, 1, 2, 4]
def baseStart_2729326 : Nat := 118140960795 + 2729326 * 2 ^ 59
def prefixEnd_2729326 : Nat := 4983230072969 + 3 ^ 40 * 2729326 * 2
def baseEnd_2729326 : Nat := 934304067208862488782043

theorem tailTrace_2729326 : CollatzResearch.WordTrace tailWord_2729326 prefixEnd_2729326 934304067208862488782043 := by
  unfold tailWord_2729326
  simp only [CollatzResearch.WordTrace]
  refine ⟨12443337163765688576907979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66364464873417005743509221 12443337163765688576907979)
  ·
    refine ⟨18665005745648532865361969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12443337163765688576907979 18665005745648532865361969)
    ·
      refine ⟨13998754309236399649021477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18665005745648532865361969 13998754309236399649021477)
      ·
        refine ⟨2624766432981824934191527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13998754309236399649021477 2624766432981824934191527)
        ·
          refine ⟨3937149649472737401287291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2624766432981824934191527 3937149649472737401287291)
          ·
            refine ⟨5905724474209106101930937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3937149649472737401287291 5905724474209106101930937)
            ·
              refine ⟨4429293355656829576448203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5905724474209106101930937 4429293355656829576448203)
              ·
                refine ⟨6643940033485244364672305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4429293355656829576448203 6643940033485244364672305)
                ·
                  refine ⟨4982955025113933273504229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6643940033485244364672305 4982955025113933273504229)
                  ·
                    refine ⟨934304067208862488782043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4982955025113933273504229 934304067208862488782043)
                    ·
                      rfl

theorem cell22_2729326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_2729326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729326 prefixEnd_2729326 := by exact prefixLift 2729326
  have htrace : WordTrace (prefixWord ++ tailWord_2729326) baseStart_2729326 baseEnd_2729326 := by
    simpa [prefixWord, tailWord_2729326, baseEnd_2729326] using wordTrace_append hprefix tailTrace_2729326
  have hstable : (prefixWord ++ tailWord_2729326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729326).length < 2 ^ (prefixWord ++ tailWord_2729326).sum := by decide
  have hdescent : baseEnd_2729326 < baseStart_2729326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729339 : List Nat := [1, 1, 1, 1, 1, 6, 2, 5, 1, 3]
def baseStart_2729339 : Nat := 118140960795 + 2729339 * 2 ^ 59
def prefixEnd_2729339 : Nat := 4983230072969 + 3 ^ 40 * 2729339 * 2
def baseEnd_2729339 : Nat := 934308517374534788207003

theorem tailTrace_2729339 : CollatzResearch.WordTrace tailWord_2729339 prefixEnd_2729339 934308517374534788207003 := by
  unfold tailWord_2729339
  simp only [CollatzResearch.WordTrace]
  refine ⟨99547171459078411835487071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66364780972718941223658047 99547171459078411835487071)
  ·
    refine ⟨149320757188617617753230607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99547171459078411835487071 149320757188617617753230607)
    ·
      refine ⟨223981135782926426629845911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149320757188617617753230607 223981135782926426629845911)
      ·
        refine ⟨335971703674389639944768867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223981135782926426629845911 335971703674389639944768867)
        ·
          refine ⟨503957555511584459917153301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335971703674389639944768867 503957555511584459917153301)
          ·
            refine ⟨23623010414605521558616561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 503957555511584459917153301 23623010414605521558616561)
            ·
              refine ⟨17717257810954141168962421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23623010414605521558616561 17717257810954141168962421)
              ·
                refine ⟨1660992919776950734590227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17717257810954141168962421 1660992919776950734590227)
                ·
                  refine ⟨2491489379665426101885341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1660992919776950734590227 2491489379665426101885341)
                  ·
                    refine ⟨934308517374534788207003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2491489379665426101885341 934308517374534788207003)
                    ·
                      rfl

theorem cell22_2729339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 5, 1, 3].length) (baseStart_2729339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729339 prefixEnd_2729339 := by exact prefixLift 2729339
  have htrace : WordTrace (prefixWord ++ tailWord_2729339) baseStart_2729339 baseEnd_2729339 := by
    simpa [prefixWord, tailWord_2729339, baseEnd_2729339] using wordTrace_append hprefix tailTrace_2729339
  have hstable : (prefixWord ++ tailWord_2729339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729339).length < 2 ^ (prefixWord ++ tailWord_2729339).sum := by decide
  have hdescent : baseEnd_2729339 < baseStart_2729339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729352 : List Nat := [2, 1, 3, 3, 1, 2, 1, 4, 5]
def baseStart_2729352 : Nat := 118140960795 + 2729352 * 2 ^ 59
def prefixEnd_2729352 : Nat := 4983230072969 + 3 ^ 40 * 2729352 * 2
def baseEnd_2729352 : Nat := 311437655846735695877321

theorem tailTrace_2729352 : CollatzResearch.WordTrace tailWord_2729352 prefixEnd_2729352 311437655846735695877321 := by
  unfold tailWord_2729352
  simp only [CollatzResearch.WordTrace]
  refine ⟨49773822804015657527855155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66365097072020876703806873 49773822804015657527855155)
  ·
    refine ⟨74660734206023486291782733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49773822804015657527855155 74660734206023486291782733)
    ·
      refine ⟨27997775327258807359418525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74660734206023486291782733 27997775327258807359418525)
      ·
        refine ⟨10499165747722052759781947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27997775327258807359418525 10499165747722052759781947)
        ·
          refine ⟨15748748621583079139672921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10499165747722052759781947 15748748621583079139672921)
          ·
            refine ⟨11811561466187309354754691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15748748621583079139672921 11811561466187309354754691)
            ·
              refine ⟨17717342199280964032132037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11811561466187309354754691 17717342199280964032132037)
              ·
                refine ⟨3322001662365180756024757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17717342199280964032132037 3322001662365180756024757)
                ·
                  refine ⟨311437655846735695877321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3322001662365180756024757 311437655846735695877321)
                  ·
                    rfl

theorem cell22_2729352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 5].length) (baseStart_2729352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729352 prefixEnd_2729352 := by exact prefixLift 2729352
  have htrace : WordTrace (prefixWord ++ tailWord_2729352) baseStart_2729352 baseEnd_2729352 := by
    simpa [prefixWord, tailWord_2729352, baseEnd_2729352] using wordTrace_append hprefix tailTrace_2729352
  have hstable : (prefixWord ++ tailWord_2729352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729352).length < 2 ^ (prefixWord ++ tailWord_2729352).sum := by decide
  have hdescent : baseEnd_2729352 < baseStart_2729352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729461 : List Nat := [1, 3, 5, 1, 1, 2, 1, 2, 2, 4]
def baseStart_2729461 : Nat := 118140960795 + 2729461 * 2 ^ 59
def prefixEnd_2729461 : Nat := 4983230072969 + 3 ^ 40 * 2729461 * 2
def baseEnd_2729461 : Nat := 934350280467767136656629

theorem tailTrace_2729461 : CollatzResearch.WordTrace tailWord_2729461 prefixEnd_2729461 934350280467767136656629 := by
  unfold tailWord_2729461
  simp only [CollatzResearch.WordTrace]
  refine ⟨99551621164636426671428237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66367747443090951114285491 99551621164636426671428237)
  ·
    refine ⟨37331857936738660001785589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99551621164636426671428237 37331857936738660001785589)
    ·
      refine ⟨3499861681569249375167399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37331857936738660001785589 3499861681569249375167399)
      ·
        refine ⟨5249792522353874062751099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3499861681569249375167399 5249792522353874062751099)
        ·
          refine ⟨7874688783530811094126649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5249792522353874062751099 7874688783530811094126649)
          ·
            refine ⟨5906016587648108320594987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7874688783530811094126649 5906016587648108320594987)
            ·
              refine ⟨8859024881472162480892481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5906016587648108320594987 8859024881472162480892481)
              ·
                refine ⟨6644268661104121860669361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8859024881472162480892481 6644268661104121860669361)
                ·
                  refine ⟨4983201495828091395502021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6644268661104121860669361 4983201495828091395502021)
                  ·
                    refine ⟨934350280467767136656629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4983201495828091395502021 934350280467767136656629)
                    ·
                      rfl

theorem cell22_2729461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_2729461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729461 prefixEnd_2729461 := by exact prefixLift 2729461
  have htrace : WordTrace (prefixWord ++ tailWord_2729461) baseStart_2729461 baseEnd_2729461 := by
    simpa [prefixWord, tailWord_2729461, baseEnd_2729461] using wordTrace_append hprefix tailTrace_2729461
  have hstable : (prefixWord ++ tailWord_2729461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729461).length < 2 ^ (prefixWord ++ tailWord_2729461).sum := by decide
  have hdescent : baseEnd_2729461 < baseStart_2729461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729525 : List Nat := [1, 3, 3, 1, 1, 5, 2, 2, 1, 3]
def baseStart_2729525 : Nat := 118140960795 + 2729525 * 2 ^ 59
def prefixEnd_2729525 : Nat := 4983230072969 + 3 ^ 40 * 2729525 * 2
def baseEnd_2729525 : Nat := 934372188975692303056433

theorem tailTrace_2729525 : CollatzResearch.WordTrace tailWord_2729525 prefixEnd_2729525 934372188975692303056433 := by
  unfold tailWord_2729525
  simp only [CollatzResearch.WordTrace]
  refine ⟨99553955436404565601758029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66369303624269710401172019 99553955436404565601758029)
  ·
    refine ⟨37332733288651712100659261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99553955436404565601758029 37332733288651712100659261)
    ·
      refine ⟨13999774983244392037747223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37332733288651712100659261 13999774983244392037747223)
      ·
        refine ⟨20999662474866588056620835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13999774983244392037747223 20999662474866588056620835)
        ·
          refine ⟨31499493712299882084931253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20999662474866588056620835 31499493712299882084931253)
          ·
            refine ⟨2953077535528113945462305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31499493712299882084931253 2953077535528113945462305)
            ·
              refine ⟨2214808151646085459096729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2953077535528113945462305 2214808151646085459096729)
              ·
                refine ⟨1661106113734564094322547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2214808151646085459096729 1661106113734564094322547)
                ·
                  refine ⟨2491659170601846141483821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1661106113734564094322547 2491659170601846141483821)
                  ·
                    refine ⟨934372188975692303056433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2491659170601846141483821 934372188975692303056433)
                    ·
                      rfl

theorem cell22_2729525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_2729525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729525 prefixEnd_2729525 := by exact prefixLift 2729525
  have htrace : WordTrace (prefixWord ++ tailWord_2729525) baseStart_2729525 baseEnd_2729525 := by
    simpa [prefixWord, tailWord_2729525, baseEnd_2729525] using wordTrace_append hprefix tailTrace_2729525
  have hstable : (prefixWord ++ tailWord_2729525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729525).length < 2 ^ (prefixWord ++ tailWord_2729525).sum := by decide
  have hdescent : baseEnd_2729525 < baseStart_2729525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729592 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 4, 7]
def baseStart_2729592 : Nat := 118140960795 + 2729592 * 2 ^ 59
def prefixEnd_2729592 : Nat := 4983230072969 + 3 ^ 40 * 2729592 * 2
def baseEnd_2729592 : Nat := 934395124444926461631227

theorem tailTrace_2729592 : CollatzResearch.WordTrace tailWord_2729592 prefixEnd_2729592 934395124444926461631227 := by
  unfold tailWord_2729592
  simp only [CollatzResearch.WordTrace]
  refine ⟨49778199563580918022223515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66370932751441224029631353 49778199563580918022223515)
  ·
    refine ⟨74667299345371377033335273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49778199563580918022223515 74667299345371377033335273)
    ·
      refine ⟨56000474509028532775001455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74667299345371377033335273 56000474509028532775001455)
      ·
        refine ⟨84000711763542799162502183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56000474509028532775001455 84000711763542799162502183)
        ·
          refine ⟨126001067645314198743753275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84000711763542799162502183 126001067645314198743753275)
          ·
            refine ⟨189001601467971298115629913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126001067645314198743753275 189001601467971298115629913)
            ·
              refine ⟨141751201100978473586722435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189001601467971298115629913 141751201100978473586722435)
              ·
                refine ⟨212626801651467710380083653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141751201100978473586722435 212626801651467710380083653)
                ·
                  refine ⟨39867525309650195696265685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 212626801651467710380083653 39867525309650195696265685)
                  ·
                    refine ⟨934395124444926461631227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39867525309650195696265685 934395124444926461631227)
                    ·
                      rfl

theorem cell22_2729592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_2729592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729592 prefixEnd_2729592 := by exact prefixLift 2729592
  have htrace : WordTrace (prefixWord ++ tailWord_2729592) baseStart_2729592 baseEnd_2729592 := by
    simpa [prefixWord, tailWord_2729592, baseEnd_2729592] using wordTrace_append hprefix tailTrace_2729592
  have hstable : (prefixWord ++ tailWord_2729592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729592).length < 2 ^ (prefixWord ++ tailWord_2729592).sum := by decide
  have hdescent : baseEnd_2729592 < baseStart_2729592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729669 : List Nat := [1, 3, 1, 1, 1, 1, 2, 5, 3, 4]
def baseStart_2729669 : Nat := 118140960795 + 2729669 * 2 ^ 59
def prefixEnd_2729669 : Nat := 4983230072969 + 3 ^ 40 * 2729669 * 2
def baseEnd_2729669 : Nat := 934421483118523927455991

theorem tailTrace_2729669 : CollatzResearch.WordTrace tailWord_2729669 prefixEnd_2729669 934421483118523927455991 := by
  unfold tailWord_2729669
  simp only [CollatzResearch.WordTrace]
  refine ⟨99559207547882878195000061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66372805031921918796666707 99559207547882878195000061)
  ·
    refine ⟨37334702830456079323125023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99559207547882878195000061 37334702830456079323125023)
    ·
      refine ⟨56002054245684118984687535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37334702830456079323125023 56002054245684118984687535)
      ·
        refine ⟨84003081368526178477031303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56002054245684118984687535 84003081368526178477031303)
        ·
          refine ⟨126004622052789267715546955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84003081368526178477031303 126004622052789267715546955)
          ·
            refine ⟨189006933079183901573320433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126004622052789267715546955 189006933079183901573320433)
            ·
              refine ⟨141755199809387926179990325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189006933079183901573320433 141755199809387926179990325)
              ·
                refine ⟨13289549982130118079374093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 141755199809387926179990325 13289549982130118079374093)
                ·
                  refine ⟨4983581243298794279765285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13289549982130118079374093 4983581243298794279765285)
                  ·
                    refine ⟨934421483118523927455991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4983581243298794279765285 934421483118523927455991)
                    ·
                      rfl

theorem cell22_2729669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_2729669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729669 prefixEnd_2729669 := by exact prefixLift 2729669
  have htrace : WordTrace (prefixWord ++ tailWord_2729669) baseStart_2729669 baseEnd_2729669 := by
    simpa [prefixWord, tailWord_2729669, baseEnd_2729669] using wordTrace_append hprefix tailTrace_2729669
  have hstable : (prefixWord ++ tailWord_2729669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729669).length < 2 ^ (prefixWord ++ tailWord_2729669).sum := by decide
  have hdescent : baseEnd_2729669 < baseStart_2729669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729729 : List Nat := [1, 2, 4, 1, 1, 1, 2, 10]
def baseStart_2729729 : Nat := 118140960795 + 2729729 * 2 ^ 59
def prefixEnd_2729729 : Nat := 4983230072969 + 3 ^ 40 * 2729729 * 2
def baseEnd_2729729 : Nat := 103826891371633752328423

theorem tailTrace_2729729 : CollatzResearch.WordTrace tailWord_2729729 prefixEnd_2729729 103826891371633752328423 := by
  unfold tailWord_2729729
  simp only [CollatzResearch.WordTrace]
  refine ⟨99561395927665508442184241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66374263951777005628122827 99561395927665508442184241)
  ·
    refine ⟨74671046945749131331638181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99561395927665508442184241 74671046945749131331638181)
    ·
      refine ⟨14000821302327962124682159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74671046945749131331638181 14000821302327962124682159)
      ·
        refine ⟨21001231953491943187023239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14000821302327962124682159 21001231953491943187023239)
        ·
          refine ⟨31501847930237914780534859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21001231953491943187023239 31501847930237914780534859)
          ·
            refine ⟨47252771895356872170802289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31501847930237914780534859 47252771895356872170802289)
            ·
              refine ⟨35439578921517654128101717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47252771895356872170802289 35439578921517654128101717)
              ·
                refine ⟨103826891371633752328423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35439578921517654128101717 103826891371633752328423)
                ·
                  rfl

theorem cell22_2729729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 10].length) (baseStart_2729729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729729 prefixEnd_2729729 := by exact prefixLift 2729729
  have htrace : WordTrace (prefixWord ++ tailWord_2729729) baseStart_2729729 baseEnd_2729729 := by
    simpa [prefixWord, tailWord_2729729, baseEnd_2729729] using wordTrace_append hprefix tailTrace_2729729
  have hstable : (prefixWord ++ tailWord_2729729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729729).length < 2 ^ (prefixWord ++ tailWord_2729729).sum := by decide
  have hdescent : baseEnd_2729729 < baseStart_2729729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729731 : List Nat := [1, 1, 1, 3, 2, 2, 5, 1, 2, 4]
def baseStart_2729731 : Nat := 118140960795 + 2729731 * 2 ^ 59
def prefixEnd_2729731 : Nat := 4983230072969 + 3 ^ 40 * 2729731 * 2
def baseEnd_2729731 : Nat := 934442706985576432405801

theorem tailTrace_2729731 : CollatzResearch.WordTrace tailWord_2729731 prefixEnd_2729731 934442706985576432405801 := by
  unfold tailWord_2729731
  simp only [CollatzResearch.WordTrace]
  refine ⟨99561468873658262783757047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66374312582438841855838031 99561468873658262783757047)
  ·
    refine ⟨149342203310487394175635571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99561468873658262783757047 149342203310487394175635571)
    ·
      refine ⟨224013304965731091263453357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149342203310487394175635571 224013304965731091263453357)
      ·
        refine ⟨84004989362149159223795009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224013304965731091263453357 84004989362149159223795009)
        ·
          refine ⟨63003742021611869417846257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84004989362149159223795009 63003742021611869417846257)
          ·
            refine ⟨47252806516208902063384693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63003742021611869417846257 47252806516208902063384693)
            ·
              refine ⟨4429950610894584568442315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47252806516208902063384693 4429950610894584568442315)
              ·
                refine ⟨6644925916341876852663473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4429950610894584568442315 6644925916341876852663473)
                ·
                  refine ⟨4983694437256407639497605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6644925916341876852663473 4983694437256407639497605)
                  ·
                    refine ⟨934442706985576432405801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4983694437256407639497605 934442706985576432405801)
                    ·
                      rfl

theorem cell22_2729731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 4].length) (baseStart_2729731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729731 prefixEnd_2729731 := by exact prefixLift 2729731
  have htrace : WordTrace (prefixWord ++ tailWord_2729731) baseStart_2729731 baseEnd_2729731 := by
    simpa [prefixWord, tailWord_2729731, baseEnd_2729731] using wordTrace_append hprefix tailTrace_2729731
  have hstable : (prefixWord ++ tailWord_2729731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729731).length < 2 ^ (prefixWord ++ tailWord_2729731).sum := by decide
  have hdescent : baseEnd_2729731 < baseStart_2729731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
