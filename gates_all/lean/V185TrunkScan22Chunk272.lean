import V185TrunkScan22Chunk271

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2424991 : List Nat := [1, 1, 2, 6, 1, 1, 4, 1, 5]
def baseStart_2424991 : Nat := 118140960795 + 2424991 * 2 ^ 59
def prefixEnd_2424991 : Nat := 4983230072969 + 3 ^ 40 * 2424991 * 2
def baseEnd_2424991 : Nat := 276707992406050432280039

theorem tailTrace_2424991 : CollatzResearch.WordTrace tailWord_2424991 prefixEnd_2424991 276707992406050432280039 := by
  unfold tailWord_2424991
  simp only [CollatzResearch.WordTrace]
  refine ⟨88446687957679237335306827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58964458638452824890204551 88446687957679237335306827)
  ·
    refine ⟨132670031936518856002960241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88446687957679237335306827 132670031936518856002960241)
    ·
      refine ⟨99502523952389142002220181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132670031936518856002960241 99502523952389142002220181)
      ·
        refine ⟨4664180810268241031354071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 99502523952389142002220181 4664180810268241031354071)
        ·
          refine ⟨6996271215402361547031107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4664180810268241031354071 6996271215402361547031107)
          ·
            refine ⟨10494406823103542320546661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6996271215402361547031107 10494406823103542320546661)
            ·
              refine ⟨1967701279331914185102499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10494406823103542320546661 1967701279331914185102499)
              ·
                refine ⟨2951551918997871277653749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1967701279331914185102499 2951551918997871277653749)
                ·
                  refine ⟨276707992406050432280039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2951551918997871277653749 276707992406050432280039)
                  ·
                    rfl

theorem cell22_2424991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 5].length) (baseStart_2424991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2424991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2424991 prefixEnd_2424991 := by exact prefixLift 2424991
  have htrace : WordTrace (prefixWord ++ tailWord_2424991) baseStart_2424991 baseEnd_2424991 := by
    simpa [prefixWord, tailWord_2424991, baseEnd_2424991] using wordTrace_append hprefix tailTrace_2424991
  have hstable : (prefixWord ++ tailWord_2424991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424991).length < 2 ^ (prefixWord ++ tailWord_2424991).sum := by decide
  have hdescent : baseEnd_2424991 < baseStart_2424991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425019 : List Nat := [1, 1, 1, 1, 1, 2, 6, 5, 4]
def baseStart_2425019 : Nat := 118140960795 + 2425019 * 2 ^ 59
def prefixEnd_2425019 : Nat := 4983230072969 + 3 ^ 40 * 2425019 * 2
def baseEnd_2425019 : Nat := 276711187396789519046677

theorem tailTrace_2425019 : CollatzResearch.WordTrace tailWord_2425019 prefixEnd_2425019 276711187396789519046677 := by
  unfold tailWord_2425019
  simp only [CollatzResearch.WordTrace]
  refine ⟨88447709201577798117326111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58965139467718532078217407 88447709201577798117326111)
  ·
    refine ⟨132671563802366697175989167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88447709201577798117326111 132671563802366697175989167)
    ·
      refine ⟨199007345703550045763983751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132671563802366697175989167 199007345703550045763983751)
      ·
        refine ⟨298511018555325068645975627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199007345703550045763983751 298511018555325068645975627)
        ·
          refine ⟨447766527832987602968963441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298511018555325068645975627 447766527832987602968963441)
          ·
            refine ⟨335824895874740702226722581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 447766527832987602968963441 335824895874740702226722581)
            ·
              refine ⟨15741791994128470416877621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 335824895874740702226722581 15741791994128470416877621)
              ·
                refine ⟨1475792999449544101582277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15741791994128470416877621 1475792999449544101582277)
                ·
                  refine ⟨276711187396789519046677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1475792999449544101582277 276711187396789519046677)
                  ·
                    rfl

theorem cell22_2425019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 5, 4].length) (baseStart_2425019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425019 prefixEnd_2425019 := by exact prefixLift 2425019
  have htrace : WordTrace (prefixWord ++ tailWord_2425019) baseStart_2425019 baseEnd_2425019 := by
    simpa [prefixWord, tailWord_2425019, baseEnd_2425019] using wordTrace_append hprefix tailTrace_2425019
  have hstable : (prefixWord ++ tailWord_2425019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425019).length < 2 ^ (prefixWord ++ tailWord_2425019).sum := by decide
  have hdescent : baseEnd_2425019 < baseStart_2425019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425032 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 3, 6]
def baseStart_2425032 : Nat := 118140960795 + 2425032 * 2 ^ 59
def prefixEnd_2425032 : Nat := 4983230072969 + 3 ^ 40 * 2425032 * 2
def baseEnd_2425032 : Nat := 830138012356040856564991

theorem tailTrace_2425032 : CollatzResearch.WordTrace tailWord_2425032 prefixEnd_2425032 830138012356040856564991 := by
  unfold tailWord_2425032
  simp only [CollatzResearch.WordTrace]
  refine ⟨44224091675265350668774675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58965455567020467558366233 44224091675265350668774675)
  ·
    refine ⟨66336137512898026003162013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44224091675265350668774675 66336137512898026003162013)
    ·
      refine ⟨24876051567336759751185755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66336137512898026003162013 24876051567336759751185755)
      ·
        refine ⟨37314077351005139626778633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24876051567336759751185755 37314077351005139626778633)
        ·
          refine ⟨27985558013253854720083975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37314077351005139626778633 27985558013253854720083975)
          ·
            refine ⟨41978337019880782080125963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27985558013253854720083975 41978337019880782080125963)
            ·
              refine ⟨62967505529821173120188945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41978337019880782080125963 62967505529821173120188945)
              ·
                refine ⟨47225629147365879840141709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62967505529821173120188945 47225629147365879840141709)
                ·
                  refine ⟨17709610930262204940053141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47225629147365879840141709 17709610930262204940053141)
                  ·
                    refine ⟨830138012356040856564991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17709610930262204940053141 830138012356040856564991)
                    ·
                      rfl

theorem cell22_2425032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_2425032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425032 prefixEnd_2425032 := by exact prefixLift 2425032
  have htrace : WordTrace (prefixWord ++ tailWord_2425032) baseStart_2425032 baseEnd_2425032 := by
    simpa [prefixWord, tailWord_2425032, baseEnd_2425032] using wordTrace_append hprefix tailTrace_2425032
  have hstable : (prefixWord ++ tailWord_2425032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425032).length < 2 ^ (prefixWord ++ tailWord_2425032).sum := by decide
  have hdescent : baseEnd_2425032 < baseStart_2425032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425096 : List Nat := [2, 1, 3, 2, 3, 1, 1, 3, 3, 3]
def baseStart_2425096 : Nat := 118140960795 + 2425096 * 2 ^ 59
def prefixEnd_2425096 : Nat := 4983230072969 + 3 ^ 40 * 2425096 * 2
def baseEnd_2425096 : Nat := 830159920863966022964795

theorem tailTrace_2425096 : CollatzResearch.WordTrace tailWord_2425096 prefixEnd_2425096 830159920863966022964795 := by
  unfold tailWord_2425096
  simp only [CollatzResearch.WordTrace]
  refine ⟨44225258811149420133939571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58967011748199226845252761 44225258811149420133939571)
  ·
    refine ⟨66337888216724130200909357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44225258811149420133939571 66337888216724130200909357)
    ·
      refine ⟨24876708081271548825341009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66337888216724130200909357 24876708081271548825341009)
      ·
        refine ⟨18657531060953661619005757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24876708081271548825341009 18657531060953661619005757)
        ·
          refine ⟨6996574147857623107127159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18657531060953661619005757 6996574147857623107127159)
          ·
            refine ⟨10494861221786434660690739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6996574147857623107127159 10494861221786434660690739)
            ·
              refine ⟨15742291832679651991036109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10494861221786434660690739 15742291832679651991036109)
              ·
                refine ⟨5903359437254869496638541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15742291832679651991036109 5903359437254869496638541)
                ·
                  refine ⟨2213759788970576061239453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5903359437254869496638541 2213759788970576061239453)
                  ·
                    refine ⟨830159920863966022964795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2213759788970576061239453 830159920863966022964795)
                    ·
                      rfl

theorem cell22_2425096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_2425096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425096 prefixEnd_2425096 := by exact prefixLift 2425096
  have htrace : WordTrace (prefixWord ++ tailWord_2425096) baseStart_2425096 baseEnd_2425096 := by
    simpa [prefixWord, tailWord_2425096, baseEnd_2425096] using wordTrace_append hprefix tailTrace_2425096
  have hstable : (prefixWord ++ tailWord_2425096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425096).length < 2 ^ (prefixWord ++ tailWord_2425096).sum := by decide
  have hdescent : baseEnd_2425096 < baseStart_2425096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425109 : List Nat := [1, 3, 2, 1, 2, 1, 2, 5, 5]
def baseStart_2425109 : Nat := 118140960795 + 2425109 * 2 ^ 59
def prefixEnd_2425109 : Nat := 4983230072969 + 3 ^ 40 * 2425109 * 2
def baseEnd_2425109 : Nat := 276721457009879440796585

theorem tailTrace_2425109 : CollatzResearch.WordTrace tailWord_2425109 prefixEnd_2425109 276721457009879440796585 := by
  unfold tailWord_2425109
  simp only [CollatzResearch.WordTrace]
  refine ⟨88450991771251743488102381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58967327847501162325401587 88450991771251743488102381)
  ·
    refine ⟨33169121914219403808038393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88450991771251743488102381 33169121914219403808038393)
    ·
      refine ⟨24876841435664552856028795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33169121914219403808038393 24876841435664552856028795)
      ·
        refine ⟨37315262153496829284043193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24876841435664552856028795 37315262153496829284043193)
        ·
          refine ⟨27986446615122621963032395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37315262153496829284043193 27986446615122621963032395)
          ·
            refine ⟨41979669922683932944548593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27986446615122621963032395 41979669922683932944548593)
            ·
              refine ⟨31484752442012949708411445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41979669922683932944548593 31484752442012949708411445)
              ·
                refine ⟨2951695541438714035163573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31484752442012949708411445 2951695541438714035163573)
                ·
                  refine ⟨276721457009879440796585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2951695541438714035163573 276721457009879440796585)
                  ·
                    rfl

theorem cell22_2425109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 5].length) (baseStart_2425109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425109 prefixEnd_2425109 := by exact prefixLift 2425109
  have htrace : WordTrace (prefixWord ++ tailWord_2425109) baseStart_2425109 baseEnd_2425109 := by
    simpa [prefixWord, tailWord_2425109, baseEnd_2425109] using wordTrace_append hprefix tailTrace_2425109
  have hstable : (prefixWord ++ tailWord_2425109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425109).length < 2 ^ (prefixWord ++ tailWord_2425109).sum := by decide
  have hdescent : baseEnd_2425109 < baseStart_2425109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425186 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 3, 5]
def baseStart_2425186 : Nat := 118140960795 + 2425186 * 2 ^ 59
def prefixEnd_2425186 : Nat := 4983230072969 + 3 ^ 40 * 2425186 * 2
def baseEnd_2425186 : Nat := 830190729703235788214519

theorem tailTrace_2425186 : CollatzResearch.WordTrace tailWord_2425186 prefixEnd_2425186 830190729703235788214519 := by
  unfold tailWord_2425186
  simp only [CollatzResearch.WordTrace]
  refine ⟨22113450047993196409663853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58969200127981857092436941 22113450047993196409663853)
  ·
    refine ⟨8292543767997448653623945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22113450047993196409663853 8292543767997448653623945)
    ·
      refine ⟨6219407825998086490217959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8292543767997448653623945 6219407825998086490217959)
      ·
        refine ⟨9329111738997129735326939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6219407825998086490217959 9329111738997129735326939)
        ·
          refine ⟨13993667608495694602990409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9329111738997129735326939 13993667608495694602990409)
          ·
            refine ⟨10495250706371770952242807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13993667608495694602990409 10495250706371770952242807)
            ·
              refine ⟨15742876059557656428364211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10495250706371770952242807 15742876059557656428364211)
              ·
                refine ⟨23614314089336484642546317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15742876059557656428364211 23614314089336484642546317)
                ·
                  refine ⟨8855367783501181740954869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23614314089336484642546317 8855367783501181740954869)
                  ·
                    refine ⟨830190729703235788214519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8855367783501181740954869 830190729703235788214519)
                    ·
                      rfl

theorem cell22_2425186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_2425186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425186 prefixEnd_2425186 := by exact prefixLift 2425186
  have htrace : WordTrace (prefixWord ++ tailWord_2425186) baseStart_2425186 baseEnd_2425186 := by
    simpa [prefixWord, tailWord_2425186, baseEnd_2425186] using wordTrace_append hprefix tailTrace_2425186
  have hstable : (prefixWord ++ tailWord_2425186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425186).length < 2 ^ (prefixWord ++ tailWord_2425186).sum := by decide
  have hdescent : baseEnd_2425186 < baseStart_2425186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425205 : List Nat := [1, 3, 4, 1, 2, 1, 4, 2, 4]
def baseStart_2425205 : Nat := 118140960795 + 2425205 * 2 ^ 59
def prefixEnd_2425205 : Nat := 4983230072969 + 3 ^ 40 * 2425205 * 2
def baseEnd_2425205 : Nat := 276732411263842023996487

theorem tailTrace_2425205 : CollatzResearch.WordTrace tailWord_2425205 prefixEnd_2425205 276732411263842023996487 := by
  unfold tailWord_2425205
  simp only [CollatzResearch.WordTrace]
  refine ⟨88454493178903951883597069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58969662119269301255731379 88454493178903951883597069)
  ·
    refine ⟨33170434942088981956348901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88454493178903951883597069 33170434942088981956348901)
    ·
      refine ⟨6219456551641684116815419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33170434942088981956348901 6219456551641684116815419)
      ·
        refine ⟨9329184827462526175223129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6219456551641684116815419 9329184827462526175223129)
        ·
          refine ⟨6996888620596894631417347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9329184827462526175223129 6996888620596894631417347)
          ·
            refine ⟨10495332930895341947126021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6996888620596894631417347 10495332930895341947126021)
            ·
              refine ⟨1967874924542876615086129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10495332930895341947126021 1967874924542876615086129)
              ·
                refine ⟨1475906193407157461314597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1967874924542876615086129 1475906193407157461314597)
                ·
                  refine ⟨276732411263842023996487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1475906193407157461314597 276732411263842023996487)
                  ·
                    rfl

theorem cell22_2425205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 2, 4].length) (baseStart_2425205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425205 prefixEnd_2425205 := by exact prefixLift 2425205
  have htrace : WordTrace (prefixWord ++ tailWord_2425205) baseStart_2425205 baseEnd_2425205 := by
    simpa [prefixWord, tailWord_2425205, baseEnd_2425205] using wordTrace_append hprefix tailTrace_2425205
  have hstable : (prefixWord ++ tailWord_2425205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425205).length < 2 ^ (prefixWord ++ tailWord_2425205).sum := by decide
  have hdescent : baseEnd_2425205 < baseStart_2425205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425265 : List Nat := [1, 2, 2, 4, 1, 2, 2, 4, 1, 3]
def baseStart_2425265 : Nat := 118140960795 + 2425265 * 2 ^ 59
def prefixEnd_2425265 : Nat := 4983230072969 + 3 ^ 40 * 2425265 * 2
def baseEnd_2425265 : Nat := 830217773017705915489277

theorem tailTrace_2425265 : CollatzResearch.WordTrace tailWord_2425265 prefixEnd_2425265 830217773017705915489277 := by
  unfold tailWord_2425265
  simp only [CollatzResearch.WordTrace]
  refine ⟨88456681558686582130781249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58971121039124388087187499 88456681558686582130781249)
  ·
    refine ⟨66342511169014936598085937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88456681558686582130781249 66342511169014936598085937)
    ·
      refine ⟨49756883376761202448564453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66342511169014936598085937 49756883376761202448564453)
      ·
        refine ⟨9329415633142725459105835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49756883376761202448564453 9329415633142725459105835)
        ·
          refine ⟨13994123449714088188658753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9329415633142725459105835 13994123449714088188658753)
          ·
            refine ⟨10495592587285566141494065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13994123449714088188658753 10495592587285566141494065)
            ·
              refine ⟨7871694440464174606120549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10495592587285566141494065 7871694440464174606120549)
              ·
                refine ⟨1475942707587032738647603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7871694440464174606120549 1475942707587032738647603)
                ·
                  refine ⟨2213914061380549107971405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1475942707587032738647603 2213914061380549107971405)
                  ·
                    refine ⟨830217773017705915489277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2213914061380549107971405 830217773017705915489277)
                    ·
                      rfl

theorem cell22_2425265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 4, 1, 3].length) (baseStart_2425265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425265 prefixEnd_2425265 := by exact prefixLift 2425265
  have htrace : WordTrace (prefixWord ++ tailWord_2425265) baseStart_2425265 baseEnd_2425265 := by
    simpa [prefixWord, tailWord_2425265, baseEnd_2425265] using wordTrace_append hprefix tailTrace_2425265
  have hstable : (prefixWord ++ tailWord_2425265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425265).length < 2 ^ (prefixWord ++ tailWord_2425265).sum := by decide
  have hdescent : baseEnd_2425265 < baseStart_2425265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425336 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 4, 4]
def baseStart_2425336 : Nat := 118140960795 + 2425336 * 2 ^ 59
def prefixEnd_2425336 : Nat := 4983230072969 + 3 ^ 40 * 2425336 * 2
def baseEnd_2425336 : Nat := 830242077768685396964059

theorem tailTrace_2425336 : CollatzResearch.WordTrace tailWord_2425336 prefixEnd_2425336 830242077768685396964059 := by
  unfold tailWord_2425336
  simp only [CollatzResearch.WordTrace]
  refine ⟨44229635570714680628307931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58972847427619574171077241 44229635570714680628307931)
  ·
    refine ⟨66344453356072020942461897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44229635570714680628307931 66344453356072020942461897)
    ·
      refine ⟨49758340017054015706846423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66344453356072020942461897 49758340017054015706846423)
      ·
        refine ⟨74637510025581023560269635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49758340017054015706846423 74637510025581023560269635)
        ·
          refine ⟨111956265038371535340404453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74637510025581023560269635 111956265038371535340404453)
          ·
            refine ⟨20991799694694662876325835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111956265038371535340404453 20991799694694662876325835)
            ·
              refine ⟨31487699542041994314488753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20991799694694662876325835 31487699542041994314488753)
              ·
                refine ⟨23615774656531495735866565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31487699542041994314488753 23615774656531495735866565)
                ·
                  refine ⟨4427957748099655450474981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23615774656531495735866565 4427957748099655450474981)
                  ·
                    refine ⟨830242077768685396964059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4427957748099655450474981 830242077768685396964059)
                    ·
                      rfl

theorem cell22_2425336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_2425336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425336 prefixEnd_2425336 := by exact prefixLift 2425336
  have htrace : WordTrace (prefixWord ++ tailWord_2425336) baseStart_2425336 baseEnd_2425336 := by
    simpa [prefixWord, tailWord_2425336, baseEnd_2425336] using wordTrace_append hprefix tailTrace_2425336
  have hstable : (prefixWord ++ tailWord_2425336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425336).length < 2 ^ (prefixWord ++ tailWord_2425336).sum := by decide
  have hdescent : baseEnd_2425336 < baseStart_2425336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425381 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 2, 6]
def baseStart_2425381 : Nat := 118140960795 + 2425381 * 2 ^ 59
def prefixEnd_2425381 : Nat := 4983230072969 + 3 ^ 40 * 2425381 * 2
def baseEnd_2425381 : Nat := 830257482188320279588921

theorem tailTrace_2425381 : CollatzResearch.WordTrace tailWord_2425381 prefixEnd_2425381 830257482188320279588921 := by
  unfold tailWord_2425381
  simp only [CollatzResearch.WordTrace]
  refine ⟨88460912426266333942003997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58973941617510889294669331 88460912426266333942003997)
  ·
    refine ⟨33172842159849875228251499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88460912426266333942003997 33172842159849875228251499)
    ·
      refine ⟨49759263239774812842377249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33172842159849875228251499 49759263239774812842377249)
      ·
        refine ⟨37319447429831109631782937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49759263239774812842377249 37319447429831109631782937)
        ·
          refine ⟨27989585572373332223837203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37319447429831109631782937 27989585572373332223837203)
          ·
            refine ⟨41984378358559998335755805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27989585572373332223837203 41984378358559998335755805)
            ·
              refine ⟨15744141884459999375908427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41984378358559998335755805 15744141884459999375908427)
              ·
                refine ⟨23616212826689999063862641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15744141884459999375908427 23616212826689999063862641)
                ·
                  refine ⟨17712159620017499297896981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23616212826689999063862641 17712159620017499297896981)
                  ·
                    refine ⟨830257482188320279588921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17712159620017499297896981 830257482188320279588921)
                    ·
                      rfl

theorem cell22_2425381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_2425381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425381 prefixEnd_2425381 := by exact prefixLift 2425381
  have htrace : WordTrace (prefixWord ++ tailWord_2425381) baseStart_2425381 baseEnd_2425381 := by
    simpa [prefixWord, tailWord_2425381, baseEnd_2425381] using wordTrace_append hprefix tailTrace_2425381
  have hstable : (prefixWord ++ tailWord_2425381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425381).length < 2 ^ (prefixWord ++ tailWord_2425381).sum := by decide
  have hdescent : baseEnd_2425381 < baseStart_2425381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425389 : List Nat := [1, 5, 4, 1, 1, 1, 2, 1, 1, 5]
def baseStart_2425389 : Nat := 118140960795 + 2425389 * 2 ^ 59
def prefixEnd_2425389 : Nat := 4983230072969 + 3 ^ 40 * 2425389 * 2
def baseEnd_2425389 : Nat := 830260220751810925388897

theorem tailTrace_2425389 : CollatzResearch.WordTrace tailWord_2425389 prefixEnd_2425389 830260220751810925388897 := by
  unfold tailWord_2425389
  simp only [CollatzResearch.WordTrace]
  refine ⟨88461204210237351308295221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58974136140158234205530147 88461204210237351308295221)
  ·
    refine ⟨8293237894709751685152677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88461204210237351308295221 8293237894709751685152677)
    ·
      refine ⟨1554982105258078440966127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8293237894709751685152677 1554982105258078440966127)
      ·
        refine ⟨2332473157887117661449191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1554982105258078440966127 2332473157887117661449191)
        ·
          refine ⟨3498709736830676492173787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2332473157887117661449191 3498709736830676492173787)
          ·
            refine ⟨5248064605246014738260681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3498709736830676492173787 5248064605246014738260681)
            ·
              refine ⟨3936048453934511053695511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5248064605246014738260681 3936048453934511053695511)
              ·
                refine ⟨5904072680901766580543267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3936048453934511053695511 5904072680901766580543267)
                ·
                  refine ⟨8856109021352649870814901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5904072680901766580543267 8856109021352649870814901)
                  ·
                    refine ⟨830260220751810925388897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8856109021352649870814901 830260220751810925388897)
                    ·
                      rfl

theorem cell22_2425389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_2425389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425389 prefixEnd_2425389 := by exact prefixLift 2425389
  have htrace : WordTrace (prefixWord ++ tailWord_2425389) baseStart_2425389 baseEnd_2425389 := by
    simpa [prefixWord, tailWord_2425389, baseEnd_2425389] using wordTrace_append hprefix tailTrace_2425389
  have hstable : (prefixWord ++ tailWord_2425389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425389).length < 2 ^ (prefixWord ++ tailWord_2425389).sum := by decide
  have hdescent : baseEnd_2425389 < baseStart_2425389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425428 : List Nat := [2, 4, 1, 1, 1, 3, 1, 2, 2, 5]
def baseStart_2425428 : Nat := 118140960795 + 2425428 * 2 ^ 59
def prefixEnd_2425428 : Nat := 4983230072969 + 3 ^ 40 * 2425428 * 2
def baseEnd_2425428 : Nat := 830273571248827823663777

theorem tailTrace_2425428 : CollatzResearch.WordTrace tailWord_2425428 prefixEnd_2425428 830273571248827823663777 := by
  unfold tailWord_2425428
  simp only [CollatzResearch.WordTrace]
  refine ⟨44231313328548030484482469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58975084438064040645976625 44231313328548030484482469)
  ·
    refine ⟨8293371249102755715840463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44231313328548030484482469 8293371249102755715840463)
    ·
      refine ⟨12440056873654133573760695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8293371249102755715840463 12440056873654133573760695)
      ·
        refine ⟨18660085310481200360641043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12440056873654133573760695 18660085310481200360641043)
        ·
          refine ⟨27990127965721800540961565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18660085310481200360641043 27990127965721800540961565)
          ·
            refine ⟨10496297987145675202860587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27990127965721800540961565 10496297987145675202860587)
            ·
              refine ⟨15744446980718512804290881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10496297987145675202860587 15744446980718512804290881)
              ·
                refine ⟨11808335235538884603218161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15744446980718512804290881 11808335235538884603218161)
                ·
                  refine ⟨8856251426654163452413621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11808335235538884603218161 8856251426654163452413621)
                  ·
                    refine ⟨830273571248827823663777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8856251426654163452413621 830273571248827823663777)
                    ·
                      rfl

theorem cell22_2425428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_2425428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425428 prefixEnd_2425428 := by exact prefixLift 2425428
  have htrace : WordTrace (prefixWord ++ tailWord_2425428) baseStart_2425428 baseEnd_2425428 := by
    simpa [prefixWord, tailWord_2425428, baseEnd_2425428] using wordTrace_append hprefix tailTrace_2425428
  have hstable : (prefixWord ++ tailWord_2425428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425428).length < 2 ^ (prefixWord ++ tailWord_2425428).sum := by decide
  have hdescent : baseEnd_2425428 < baseStart_2425428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425473 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 3, 5]
def baseStart_2425473 : Nat := 118140960795 + 2425473 * 2 ^ 59
def prefixEnd_2425473 : Nat := 4983230072969 + 3 ^ 40 * 2425473 * 2
def baseEnd_2425473 : Nat := 830288975668462706288639

theorem tailTrace_2425473 : CollatzResearch.WordTrace tailWord_2425473 prefixEnd_2425473 830288975668462706288639 := by
  unfold tailWord_2425473
  simp only [CollatzResearch.WordTrace]
  refine ⟨88464267941933033654353073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58976178627955355769568715 88464267941933033654353073)
  ·
    refine ⟨66348200956449775240764805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88464267941933033654353073 66348200956449775240764805)
    ·
      refine ⟨12440287679334332857643401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66348200956449775240764805 12440287679334332857643401)
      ·
        refine ⟨9330215759500749643232551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12440287679334332857643401 9330215759500749643232551)
        ·
          refine ⟨13995323639251124464848827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9330215759500749643232551 13995323639251124464848827)
          ·
            refine ⟨20992985458876686697273241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13995323639251124464848827 20992985458876686697273241)
            ·
              refine ⟨15744739094157515022954931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20992985458876686697273241 15744739094157515022954931)
              ·
                refine ⟨23617108641236272534432397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15744739094157515022954931 23617108641236272534432397)
                ·
                  refine ⟨8856415740463602200412149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23617108641236272534432397 8856415740463602200412149)
                  ·
                    refine ⟨830288975668462706288639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8856415740463602200412149 830288975668462706288639)
                    ·
                      rfl

theorem cell22_2425473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_2425473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425473 prefixEnd_2425473 := by exact prefixLift 2425473
  have htrace : WordTrace (prefixWord ++ tailWord_2425473) baseStart_2425473 baseEnd_2425473 := by
    simpa [prefixWord, tailWord_2425473, baseEnd_2425473] using wordTrace_append hprefix tailTrace_2425473
  have hstable : (prefixWord ++ tailWord_2425473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425473).length < 2 ^ (prefixWord ++ tailWord_2425473).sum := by decide
  have hdescent : baseEnd_2425473 < baseStart_2425473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425475 : List Nat := [1, 1, 1, 3, 3, 1, 5, 3, 4]
def baseStart_2425475 : Nat := 118140960795 + 2425475 * 2 ^ 59
def prefixEnd_2425475 : Nat := 4983230072969 + 3 ^ 40 * 2425475 * 2
def baseEnd_2425475 : Nat := 276763220103111789246211

theorem tailTrace_2425475 : CollatzResearch.WordTrace tailWord_2425475 prefixEnd_2425475 276763220103111789246211 := by
  unfold tailWord_2425475
  simp only [CollatzResearch.WordTrace]
  refine ⟨88464340887925787995925879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58976227258617191997283919 88464340887925787995925879)
  ·
    refine ⟨132696511331888681993888819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88464340887925787995925879 132696511331888681993888819)
    ·
      refine ⟨199044766997833022990833229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132696511331888681993888819 199044766997833022990833229)
      ·
        refine ⟨74641787624187383621562461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199044766997833022990833229 74641787624187383621562461)
        ·
          refine ⟨27990670359070268858085923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74641787624187383621562461 27990670359070268858085923)
          ·
            refine ⟨41986005538605403287128885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27990670359070268858085923 41986005538605403287128885)
            ·
              refine ⟨3936188019244256558168333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41986005538605403287128885 3936188019244256558168333)
              ·
                refine ⟨1476070507216596209313125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3936188019244256558168333 1476070507216596209313125)
                ·
                  refine ⟨276763220103111789246211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1476070507216596209313125 276763220103111789246211)
                  ·
                    rfl

theorem cell22_2425475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 3, 4].length) (baseStart_2425475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425475 prefixEnd_2425475 := by exact prefixLift 2425475
  have htrace : WordTrace (prefixWord ++ tailWord_2425475) baseStart_2425475 baseEnd_2425475 := by
    simpa [prefixWord, tailWord_2425475, baseEnd_2425475] using wordTrace_append hprefix tailTrace_2425475
  have hstable : (prefixWord ++ tailWord_2425475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425475).length < 2 ^ (prefixWord ++ tailWord_2425475).sum := by decide
  have hdescent : baseEnd_2425475 < baseStart_2425475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425492 : List Nat := [2, 4, 2, 2, 1, 3, 1, 1, 6]
def baseStart_2425492 : Nat := 118140960795 + 2425492 * 2 ^ 59
def prefixEnd_2425492 : Nat := 4983230072969 + 3 ^ 40 * 2425492 * 2
def baseEnd_2425492 : Nat := 276765159918917663354527

theorem tailTrace_2425492 : CollatzResearch.WordTrace tailWord_2425492 prefixEnd_2425492 276765159918917663354527 := by
  unfold tailWord_2425492
  simp only [CollatzResearch.WordTrace]
  refine ⟨44232480464432099949647365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58976640619242799932863153 44232480464432099949647365)
  ·
    refine ⟨8293590087081018740558881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44232480464432099949647365 8293590087081018740558881)
    ·
      refine ⟨6220192565310764055419161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8293590087081018740558881 6220192565310764055419161)
      ·
        refine ⟨4665144423983073041564371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6220192565310764055419161 4665144423983073041564371)
        ·
          refine ⟨6997716635974609562346557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4665144423983073041564371 6997716635974609562346557)
          ·
            refine ⟨2624143738490478585879959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6997716635974609562346557 2624143738490478585879959)
            ·
              refine ⟨3936215607735717878819939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2624143738490478585879959 3936215607735717878819939)
              ·
                refine ⟨5904323411603576818229909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3936215607735717878819939 5904323411603576818229909)
                ·
                  refine ⟨276765159918917663354527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5904323411603576818229909 276765159918917663354527)
                  ·
                    rfl

theorem cell22_2425492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_2425492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425492 prefixEnd_2425492 := by exact prefixLift 2425492
  have htrace : WordTrace (prefixWord ++ tailWord_2425492) baseStart_2425492 baseEnd_2425492 := by
    simpa [prefixWord, tailWord_2425492, baseEnd_2425492] using wordTrace_append hprefix tailTrace_2425492
  have hstable : (prefixWord ++ tailWord_2425492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425492).length < 2 ^ (prefixWord ++ tailWord_2425492).sum := by decide
  have hdescent : baseEnd_2425492 < baseStart_2425492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425511 : List Nat := [1, 1, 6, 3, 2, 1, 1, 2, 1, 4]
def baseStart_2425511 : Nat := 118140960795 + 2425511 * 2 ^ 59
def prefixEnd_2425511 : Nat := 4983230072969 + 3 ^ 40 * 2425511 * 2
def baseEnd_2425511 : Nat := 830301983845043273838523

theorem tailTrace_2425511 : CollatzResearch.WordTrace tailWord_2425511 prefixEnd_2425511 830301983845043273838523 := by
  unfold tailWord_2425511
  simp only [CollatzResearch.WordTrace]
  refine ⟨88465653915795366144236387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58977102610530244096157591 88465653915795366144236387)
  ·
    refine ⟨132698480873693049216354581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88465653915795366144236387 132698480873693049216354581)
    ·
      refine ⟨6220241290954361682016621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 132698480873693049216354581 6220241290954361682016621)
      ·
        refine ⟨2332590484107885630756233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6220241290954361682016621 2332590484107885630756233)
        ·
          refine ⟨1749442863080914223067175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2332590484107885630756233 1749442863080914223067175)
          ·
            refine ⟨2624164294621371334600763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1749442863080914223067175 2624164294621371334600763)
            ·
              refine ⟨3936246441932057001901145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2624164294621371334600763 3936246441932057001901145)
              ·
                refine ⟨2952184831449042751425859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3936246441932057001901145 2952184831449042751425859)
                ·
                  refine ⟨4428277247173564127138789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2952184831449042751425859 4428277247173564127138789)
                  ·
                    refine ⟨830301983845043273838523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4428277247173564127138789 830301983845043273838523)
                    ·
                      rfl

theorem cell22_2425511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_2425511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425511 prefixEnd_2425511 := by exact prefixLift 2425511
  have htrace : WordTrace (prefixWord ++ tailWord_2425511) baseStart_2425511 baseEnd_2425511 := by
    simpa [prefixWord, tailWord_2425511, baseEnd_2425511] using wordTrace_append hprefix tailTrace_2425511
  have hstable : (prefixWord ++ tailWord_2425511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425511).length < 2 ^ (prefixWord ++ tailWord_2425511).sum := by decide
  have hdescent : baseEnd_2425511 < baseStart_2425511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425537 : List Nat := [1, 2, 6, 2, 2, 9]
def baseStart_2425537 : Nat := 118140960795 + 2425537 * 2 ^ 59
def prefixEnd_2425537 : Nat := 4983230072969 + 3 ^ 40 * 2425537 * 2
def baseEnd_2425537 : Nat := 10250751656498615712203

theorem tailTrace_2425537 : CollatzResearch.WordTrace tailWord_2425537 prefixEnd_2425537 10250751656498615712203 := by
  unfold tailWord_2425537
  simp only [CollatzResearch.WordTrace]
  refine ⟨88466602213701172584682865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58977734809134115056455243 88466602213701172584682865)
  ·
    refine ⟨66349951660275879438512149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88466602213701172584682865 66349951660275879438512149)
    ·
      refine ⟨3110153984075431848680257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 66349951660275879438512149 3110153984075431848680257)
      ·
        refine ⟨2332615488056573886510193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3110153984075431848680257 2332615488056573886510193)
        ·
          refine ⟨1749461616042430414882645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2332615488056573886510193 1749461616042430414882645)
          ·
            refine ⟨10250751656498615712203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1749461616042430414882645 10250751656498615712203)
            ·
              rfl

theorem cell22_2425537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 9].length) (baseStart_2425537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425537 prefixEnd_2425537 := by exact prefixLift 2425537
  have htrace : WordTrace (prefixWord ++ tailWord_2425537) baseStart_2425537 baseEnd_2425537 := by
    simpa [prefixWord, tailWord_2425537, baseEnd_2425537] using wordTrace_append hprefix tailTrace_2425537
  have hstable : (prefixWord ++ tailWord_2425537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425537).length < 2 ^ (prefixWord ++ tailWord_2425537).sum := by decide
  have hdescent : baseEnd_2425537 < baseStart_2425537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425610 : List Nat := [3, 1, 2, 2, 1, 2, 4, 1, 6]
def baseStart_2425610 : Nat := 118140960795 + 2425610 * 2 ^ 59
def prefixEnd_2425610 : Nat := 4983230072969 + 3 ^ 40 * 2425610 * 2
def baseEnd_2425610 : Nat := 276778624522746671871073

theorem tailTrace_2425610 : CollatzResearch.WordTrace tailWord_2425610 prefixEnd_2425610 276778624522746671871073 := by
  unfold tailWord_2425610
  simp only [CollatzResearch.WordTrace]
  refine ⟨22117316185609176513022571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58979509828291137368060189 22117316185609176513022571)
  ·
    refine ⟨33175974278413764769533857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22117316185609176513022571 33175974278413764769533857)
    ·
      refine ⟨24881980708810323577150393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33175974278413764769533857 24881980708810323577150393)
      ·
        refine ⟨18661485531607742682862795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24881980708810323577150393 18661485531607742682862795)
        ·
          refine ⟨27992228297411614024294193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18661485531607742682862795 27992228297411614024294193)
          ·
            refine ⟨20994171223058710518220645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27992228297411614024294193 20994171223058710518220645)
            ·
              refine ⟨3936407104323508222166371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20994171223058710518220645 3936407104323508222166371)
              ·
                refine ⟨5904610656485262333249557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3936407104323508222166371 5904610656485262333249557)
                ·
                  refine ⟨276778624522746671871073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5904610656485262333249557 276778624522746671871073)
                  ·
                    rfl

theorem cell22_2425610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 6].length) (baseStart_2425610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425610 prefixEnd_2425610 := by exact prefixLift 2425610
  have htrace : WordTrace (prefixWord ++ tailWord_2425610) baseStart_2425610 baseEnd_2425610 := by
    simpa [prefixWord, tailWord_2425610, baseEnd_2425610] using wordTrace_append hprefix tailTrace_2425610
  have hstable : (prefixWord ++ tailWord_2425610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425610).length < 2 ^ (prefixWord ++ tailWord_2425610).sum := by decide
  have hdescent : baseEnd_2425610 < baseStart_2425610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425640 : List Nat := [2, 1, 5, 1, 1, 1, 1, 3, 1, 6]
def baseStart_2425640 : Nat := 118140960795 + 2425640 * 2 ^ 59
def prefixEnd_2425640 : Nat := 4983230072969 + 3 ^ 40 * 2425640 * 2
def baseEnd_2425640 : Nat := 830346143181329937363127

theorem tailTrace_2425640 : CollatzResearch.WordTrace tailWord_2425640 prefixEnd_2425640 830346143181329937363127 := by
  unfold tailWord_2425640
  simp only [CollatzResearch.WordTrace]
  refine ⟨44235179466164010587841187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58980239288218680783788249 44235179466164010587841187)
  ·
    refine ⟨66352769199246015881761781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44235179466164010587841187 66352769199246015881761781)
    ·
      refine ⟨6220572112429313988915167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66352769199246015881761781 6220572112429313988915167)
      ·
        refine ⟨9330858168643970983372751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6220572112429313988915167 9330858168643970983372751)
        ·
          refine ⟨13996287252965956475059127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9330858168643970983372751 13996287252965956475059127)
          ·
            refine ⟨20994430879448934712588691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13996287252965956475059127 20994430879448934712588691)
            ·
              refine ⟨31491646319173402068883037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20994430879448934712588691 31491646319173402068883037)
              ·
                refine ⟨11809367369690025775831139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31491646319173402068883037 11809367369690025775831139)
                ·
                  refine ⟨17714051054535038663746709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11809367369690025775831139 17714051054535038663746709)
                  ·
                    refine ⟨830346143181329937363127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17714051054535038663746709 830346143181329937363127)
                    ·
                      rfl

theorem cell22_2425640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_2425640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425640 prefixEnd_2425640 := by exact prefixLift 2425640
  have htrace : WordTrace (prefixWord ++ tailWord_2425640) baseStart_2425640 baseEnd_2425640 := by
    simpa [prefixWord, tailWord_2425640, baseEnd_2425640] using wordTrace_append hprefix tailTrace_2425640
  have hstable : (prefixWord ++ tailWord_2425640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425640).length < 2 ^ (prefixWord ++ tailWord_2425640).sum := by decide
  have hdescent : baseEnd_2425640 < baseStart_2425640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425661 : List Nat := [1, 4, 1, 4, 2, 1, 3, 2, 4]
def baseStart_2425661 : Nat := 118140960795 + 2425661 * 2 ^ 59
def prefixEnd_2425661 : Nat := 4983230072969 + 3 ^ 40 * 2425661 * 2
def baseEnd_2425661 : Nat := 276784443970164294196021

theorem tailTrace_2425661 : CollatzResearch.WordTrace tailWord_2425661 prefixEnd_2425661 276784443970164294196021 := by
  unfold tailWord_2425661
  simp only [CollatzResearch.WordTrace]
  refine ⟨88471124865251941762196837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58980749910167961174797891 88471124865251941762196837)
  ·
    refine ⟨16588335912234739080411907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88471124865251941762196837 16588335912234739080411907)
    ·
      refine ⟨24882503868352108620617861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16588335912234739080411907 24882503868352108620617861)
      ·
        refine ⟨4665469475316020366365849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24882503868352108620617861 4665469475316020366365849)
        ·
          refine ⟨3499102106487015274774387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4665469475316020366365849 3499102106487015274774387)
          ·
            refine ⟨5248653159730522912161581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3499102106487015274774387 5248653159730522912161581)
            ·
              refine ⟨1968244934898946092060593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5248653159730522912161581 1968244934898946092060593)
              ·
                refine ⟨1476183701174209569045445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1968244934898946092060593 1476183701174209569045445)
                ·
                  refine ⟨276784443970164294196021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1476183701174209569045445 276784443970164294196021)
                  ·
                    rfl

theorem cell22_2425661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_2425661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425661 prefixEnd_2425661 := by exact prefixLift 2425661
  have htrace : WordTrace (prefixWord ++ tailWord_2425661) baseStart_2425661 baseEnd_2425661 := by
    simpa [prefixWord, tailWord_2425661, baseEnd_2425661] using wordTrace_append hprefix tailTrace_2425661
  have hstable : (prefixWord ++ tailWord_2425661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425661).length < 2 ^ (prefixWord ++ tailWord_2425661).sum := by decide
  have hdescent : baseEnd_2425661 < baseStart_2425661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425676 : List Nat := [2, 2, 1, 3, 3, 3, 2, 1, 2, 3]
def baseStart_2425676 : Nat := 118140960795 + 2425676 * 2 ^ 59
def prefixEnd_2425676 : Nat := 4983230072969 + 3 ^ 40 * 2425676 * 2
def baseEnd_2425676 : Nat := 830358466717037843463017

theorem tailTrace_2425676 : CollatzResearch.WordTrace tailWord_2425676 prefixEnd_2425676 830358466717037843463017 := by
  unfold tailWord_2425676
  simp only [CollatzResearch.WordTrace]
  refine ⟨44235835980098799661996441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58981114640131732882661921 44235835980098799661996441)
  ·
    refine ⟨33176876985074099746497331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44235835980098799661996441 33176876985074099746497331)
    ·
      refine ⟨49765315477611149619745997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33176876985074099746497331 49765315477611149619745997)
      ·
        refine ⟨18661993304104181107404749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49765315477611149619745997 18661993304104181107404749)
        ·
          refine ⟨6998247489039067915276781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18661993304104181107404749 6998247489039067915276781)
          ·
            refine ⟨2624342808389650468228793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6998247489039067915276781 2624342808389650468228793)
            ·
              refine ⟨1968257106292237851171595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2624342808389650468228793 1968257106292237851171595)
              ·
                refine ⟨2952385659438356776757393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1968257106292237851171595 2952385659438356776757393)
                ·
                  refine ⟨2214289244578767582568045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2952385659438356776757393 2214289244578767582568045)
                  ·
                    refine ⟨830358466717037843463017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2214289244578767582568045 830358466717037843463017)
                    ·
                      rfl

theorem cell22_2425676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 2, 3].length) (baseStart_2425676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425676 prefixEnd_2425676 := by exact prefixLift 2425676
  have htrace : WordTrace (prefixWord ++ tailWord_2425676) baseStart_2425676 baseEnd_2425676 := by
    simpa [prefixWord, tailWord_2425676, baseEnd_2425676] using wordTrace_append hprefix tailTrace_2425676
  have hstable : (prefixWord ++ tailWord_2425676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425676).length < 2 ^ (prefixWord ++ tailWord_2425676).sum := by decide
  have hdescent : baseEnd_2425676 < baseStart_2425676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425717 : List Nat := [1, 3, 4, 1, 1, 2, 1, 4, 5]
def baseStart_2425717 : Nat := 118140960795 + 2425717 * 2 ^ 59
def prefixEnd_2425717 : Nat := 4983230072969 + 3 ^ 40 * 2425717 * 2
def baseEnd_2425717 : Nat := 276790833951642467729297

theorem tailTrace_2425717 : CollatzResearch.WordTrace tailWord_2425717 prefixEnd_2425717 276790833951642467729297 := by
  unfold tailWord_2425717
  simp only [CollatzResearch.WordTrace]
  refine ⟨88473167353049063326235405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58982111568699375550823603 88473167353049063326235405)
  ·
    refine ⟨33177437757393398747338277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88473167353049063326235405 33177437757393398747338277)
    ·
      refine ⟨6220769579511262265125927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33177437757393398747338277 6220769579511262265125927)
      ·
        refine ⟨9331154369266893397688891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6220769579511262265125927 9331154369266893397688891)
        ·
          refine ⟨13996731553900340096533337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9331154369266893397688891 13996731553900340096533337)
          ·
            refine ⟨10497548665425255072400003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13996731553900340096533337 10497548665425255072400003)
            ·
              refine ⟨15746322998137882608600005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10497548665425255072400003 15746322998137882608600005)
              ·
                refine ⟨2952435562150852989112501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15746322998137882608600005 2952435562150852989112501)
                ·
                  refine ⟨276790833951642467729297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2952435562150852989112501 276790833951642467729297)
                  ·
                    rfl

theorem cell22_2425717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 5].length) (baseStart_2425717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425717 prefixEnd_2425717 := by exact prefixLift 2425717
  have htrace : WordTrace (prefixWord ++ tailWord_2425717) baseStart_2425717 baseEnd_2425717 := by
    simpa [prefixWord, tailWord_2425717, baseEnd_2425717] using wordTrace_append hprefix tailTrace_2425717
  have hstable : (prefixWord ++ tailWord_2425717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425717).length < 2 ^ (prefixWord ++ tailWord_2425717).sum := by decide
  have hdescent : baseEnd_2425717 < baseStart_2425717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425721 : List Nat := [1, 2, 1, 3, 2, 3, 4, 2, 1, 3]
def baseStart_2425721 : Nat := 118140960795 + 2425721 * 2 ^ 59
def prefixEnd_2425721 : Nat := 4983230072969 + 3 ^ 40 * 2425721 * 2
def baseEnd_2425721 : Nat := 830373871136672726087879

theorem tailTrace_2425721 : CollatzResearch.WordTrace tailWord_2425721 prefixEnd_2425721 830373871136672726087879 := by
  unfold tailWord_2425721
  simp only [CollatzResearch.WordTrace]
  refine ⟨88473313245034572009381017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58982208830023048006254011 88473313245034572009381017)
  ·
    refine ⟨66354984933775929007035763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88473313245034572009381017 66354984933775929007035763)
    ·
      refine ⟨99532477400663893510553645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66354984933775929007035763 99532477400663893510553645)
      ·
        refine ⟨37324679025248960066457617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99532477400663893510553645 37324679025248960066457617)
        ·
          refine ⟨27993509268936720049843213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37324679025248960066457617 27993509268936720049843213)
          ·
            refine ⟨10497565975851270018691205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27993509268936720049843213 10497565975851270018691205)
            ·
              refine ⟨1968293620472113128504601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10497565975851270018691205 1968293620472113128504601)
              ·
                refine ⟨1476220215354084846378451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1968293620472113128504601 1476220215354084846378451)
                ·
                  refine ⟨2214330323031127269567677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1476220215354084846378451 2214330323031127269567677)
                  ·
                    refine ⟨830373871136672726087879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2214330323031127269567677 830373871136672726087879)
                    ·
                      rfl

theorem cell22_2425721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2, 1, 3].length) (baseStart_2425721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425721 prefixEnd_2425721 := by exact prefixLift 2425721
  have htrace : WordTrace (prefixWord ++ tailWord_2425721) baseStart_2425721 baseEnd_2425721 := by
    simpa [prefixWord, tailWord_2425721, baseEnd_2425721] using wordTrace_append hprefix tailTrace_2425721
  have hstable : (prefixWord ++ tailWord_2425721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425721).length < 2 ^ (prefixWord ++ tailWord_2425721).sum := by decide
  have hdescent : baseEnd_2425721 < baseStart_2425721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425807 : List Nat := [1, 1, 2, 1, 1, 6, 4, 6]
def baseStart_2425807 : Nat := 118140960795 + 2425807 * 2 ^ 59
def prefixEnd_2425807 : Nat := 4983230072969 + 3 ^ 40 * 2425807 * 2
def baseEnd_2425807 : Nat := 92267034521577463159735

theorem tailTrace_2425807 : CollatzResearch.WordTrace tailWord_2425807 prefixEnd_2425807 92267034521577463159735 := by
  unfold tailWord_2425807
  simp only [CollatzResearch.WordTrace]
  refine ⟨88476449922723008697011675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58984299948482005798007783 88476449922723008697011675)
  ·
    refine ⟨132714674884084513045517513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88476449922723008697011675 132714674884084513045517513)
    ·
      refine ⟨99536006163063384784138135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132714674884084513045517513 99536006163063384784138135)
      ·
        refine ⟨149304009244595077176207203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99536006163063384784138135 149304009244595077176207203)
        ·
          refine ⟨223956013866892615764310805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149304009244595077176207203 223956013866892615764310805)
          ·
            refine ⟨10497938150010591363952069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 223956013866892615764310805 10497938150010591363952069)
            ·
              refine ⟨1968363403126985880741013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10497938150010591363952069 1968363403126985880741013)
              ·
                refine ⟨92267034521577463159735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1968363403126985880741013 92267034521577463159735)
                ·
                  rfl

theorem cell22_2425807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 6].length) (baseStart_2425807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425807 prefixEnd_2425807 := by exact prefixLift 2425807
  have htrace : WordTrace (prefixWord ++ tailWord_2425807) baseStart_2425807 baseEnd_2425807 := by
    simpa [prefixWord, tailWord_2425807, baseEnd_2425807] using wordTrace_append hprefix tailTrace_2425807
  have hstable : (prefixWord ++ tailWord_2425807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425807).length < 2 ^ (prefixWord ++ tailWord_2425807).sum := by decide
  have hdescent : baseEnd_2425807 < baseStart_2425807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425813 : List Nat := [1, 3, 2, 3, 4, 1, 1, 3, 4]
def baseStart_2425813 : Nat := 118140960795 + 2425813 * 2 ^ 59
def prefixEnd_2425813 : Nat := 4983230072969 + 3 ^ 40 * 2425813 * 2
def baseEnd_2425813 : Nat := 276801788205605050929199

theorem tailTrace_2425813 : CollatzResearch.WordTrace tailWord_2425813 prefixEnd_2425813 276801788205605050929199 := by
  unfold tailWord_2425813
  simp only [CollatzResearch.WordTrace]
  refine ⟨88476668760701271721730093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58984445840467514481153395 88476668760701271721730093)
  ·
    refine ⟨33178750785262976895648785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88476668760701271721730093 33178750785262976895648785)
    ·
      refine ⟨24884063088947232671736589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33178750785262976895648785 24884063088947232671736589)
      ·
        refine ⟨9331523658355212251901221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24884063088947232671736589 9331523658355212251901221)
        ·
          refine ⟨1749660685941602297231479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9331523658355212251901221 1749660685941602297231479)
          ·
            refine ⟨2624491028912403445847219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1749660685941602297231479 2624491028912403445847219)
            ·
              refine ⟨3936736543368605168770829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2624491028912403445847219 3936736543368605168770829)
              ·
                refine ⟨1476276203763226938289061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3936736543368605168770829 1476276203763226938289061)
                ·
                  refine ⟨276801788205605050929199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1476276203763226938289061 276801788205605050929199)
                  ·
                    rfl

theorem cell22_2425813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 3, 4].length) (baseStart_2425813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425813 prefixEnd_2425813 := by exact prefixLift 2425813
  have htrace : WordTrace (prefixWord ++ tailWord_2425813) baseStart_2425813 baseEnd_2425813 := by
    simpa [prefixWord, tailWord_2425813, baseEnd_2425813] using wordTrace_append hprefix tailTrace_2425813
  have hstable : (prefixWord ++ tailWord_2425813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425813).length < 2 ^ (prefixWord ++ tailWord_2425813).sum := by decide
  have hdescent : baseEnd_2425813 < baseStart_2425813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425826 : List Nat := [3, 3, 3, 1, 1, 2, 1, 2, 2, 4]
def baseStart_2425826 : Nat := 118140960795 + 2425826 * 2 ^ 59
def prefixEnd_2425826 : Nat := 4983230072969 + 3 ^ 40 * 2425826 * 2
def baseEnd_2425826 : Nat := 830409814782487452212557

theorem tailTrace_2425826 : CollatzResearch.WordTrace tailWord_2425826 prefixEnd_2425826 830409814782487452212557 := by
  unfold tailWord_2425826
  simp only [CollatzResearch.WordTrace]
  refine ⟨22119285727413543735488333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58984761939769449961302221 22119285727413543735488333)
  ·
    refine ⟨8294732147780078900808125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22119285727413543735488333 8294732147780078900808125)
    ·
      refine ⟨3110524555417529587803047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8294732147780078900808125 3110524555417529587803047)
      ·
        refine ⟨4665786833126294381704571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3110524555417529587803047 4665786833126294381704571)
        ·
          refine ⟨6998680249689441572556857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4665786833126294381704571 6998680249689441572556857)
          ·
            refine ⟨5249010187267081179417643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6998680249689441572556857 5249010187267081179417643)
            ·
              refine ⟨7873515280900621769126465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5249010187267081179417643 7873515280900621769126465)
              ·
                refine ⟨5905136460675466326844849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7873515280900621769126465 5905136460675466326844849)
                ·
                  refine ⟨4428852345506599745133637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5905136460675466326844849 4428852345506599745133637)
                  ·
                    refine ⟨830409814782487452212557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4428852345506599745133637 830409814782487452212557)
                    ·
                      rfl

theorem cell22_2425826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_2425826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425826 prefixEnd_2425826 := by exact prefixLift 2425826
  have htrace : WordTrace (prefixWord ++ tailWord_2425826) baseStart_2425826 baseEnd_2425826 := by
    simpa [prefixWord, tailWord_2425826, baseEnd_2425826] using wordTrace_append hprefix tailTrace_2425826
  have hstable : (prefixWord ++ tailWord_2425826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425826).length < 2 ^ (prefixWord ++ tailWord_2425826).sum := by decide
  have hdescent : baseEnd_2425826 < baseStart_2425826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425839 : List Nat := [1, 1, 2, 1, 4, 3, 3, 1, 3, 3]
def baseStart_2425839 : Nat := 118140960795 + 2425839 * 2 ^ 59
def prefixEnd_2425839 : Nat := 4983230072969 + 3 ^ 40 * 2425839 * 2
def baseEnd_2425839 : Nat := 830414264948159751637517

theorem tailTrace_2425839 : CollatzResearch.WordTrace tailWord_2425839 prefixEnd_2425839 830414264948159751637517 := by
  unfold tailWord_2425839
  simp only [CollatzResearch.WordTrace]
  refine ⟨88477617058607078162176571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58985078039071385441451047 88477617058607078162176571)
  ·
    refine ⟨132716425587910617243264857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88477617058607078162176571 132716425587910617243264857)
    ·
      refine ⟨99537319190932962932448643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132716425587910617243264857 99537319190932962932448643)
      ·
        refine ⟨149305978786399444398672965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99537319190932962932448643 149305978786399444398672965)
        ·
          refine ⟨27994871022449895824751181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149305978786399444398672965 27994871022449895824751181)
          ·
            refine ⟨10498076633418710934281693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27994871022449895824751181 10498076633418710934281693)
            ·
              refine ⟨3936778737532016600355635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10498076633418710934281693 3936778737532016600355635)
              ·
                refine ⟨5905168106298024900533453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3936778737532016600355635 5905168106298024900533453)
                ·
                  refine ⟨2214438039861759337700045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5905168106298024900533453 2214438039861759337700045)
                  ·
                    refine ⟨830414264948159751637517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2214438039861759337700045 830414264948159751637517)
                    ·
                      rfl

theorem cell22_2425839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 3, 3].length) (baseStart_2425839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425839 prefixEnd_2425839 := by exact prefixLift 2425839
  have htrace : WordTrace (prefixWord ++ tailWord_2425839) baseStart_2425839 baseEnd_2425839 := by
    simpa [prefixWord, tailWord_2425839, baseEnd_2425839] using wordTrace_append hprefix tailTrace_2425839
  have hstable : (prefixWord ++ tailWord_2425839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425839).length < 2 ^ (prefixWord ++ tailWord_2425839).sum := by decide
  have hdescent : baseEnd_2425839 < baseStart_2425839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425890 : List Nat := [3, 3, 1, 1, 1, 5, 2, 2, 1, 3]
def baseStart_2425890 : Nat := 118140960795 + 2425890 * 2 ^ 59
def prefixEnd_2425890 : Nat := 4983230072969 + 3 ^ 40 * 2425890 * 2
def baseEnd_2425890 : Nat := 830431723290412618612361

theorem tailTrace_2425890 : CollatzResearch.WordTrace tailWord_2425890 prefixEnd_2425890 830431723290412618612361 := by
  unfold tailWord_2425890
  simp only [CollatzResearch.WordTrace]
  refine ⟨22119869295355578468070781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58986318120948209248188749 22119869295355578468070781)
  ·
    refine ⟨8294950985758341925526543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22119869295355578468070781 8294950985758341925526543)
    ·
      refine ⟨12442426478637512888289815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8294950985758341925526543 12442426478637512888289815)
      ·
        refine ⟨18663639717956269332434723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12442426478637512888289815 18663639717956269332434723)
        ·
          refine ⟨27995459576934403998652085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18663639717956269332434723 27995459576934403998652085)
          ·
            refine ⟨2624574335337600374873633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27995459576934403998652085 2624574335337600374873633)
            ·
              refine ⟨1968430751503200281155225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2624574335337600374873633 1968430751503200281155225)
              ·
                refine ⟨1476323063627400210866419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1968430751503200281155225 1476323063627400210866419)
                ·
                  refine ⟨2214484595441100316299629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1476323063627400210866419 2214484595441100316299629)
                  ·
                    refine ⟨830431723290412618612361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2214484595441100316299629 830431723290412618612361)
                    ·
                      rfl

theorem cell22_2425890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_2425890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425890 prefixEnd_2425890 := by exact prefixLift 2425890
  have htrace : WordTrace (prefixWord ++ tailWord_2425890) baseStart_2425890 baseEnd_2425890 := by
    simpa [prefixWord, tailWord_2425890, baseEnd_2425890] using wordTrace_append hprefix tailTrace_2425890
  have hstable : (prefixWord ++ tailWord_2425890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425890).length < 2 ^ (prefixWord ++ tailWord_2425890).sum := by decide
  have hdescent : baseEnd_2425890 < baseStart_2425890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425933 : List Nat := [1, 6, 1, 1, 1, 2, 4, 1, 1, 4]
def baseStart_2425933 : Nat := 118140960795 + 2425933 * 2 ^ 59
def prefixEnd_2425933 : Nat := 4983230072969 + 3 ^ 40 * 2425933 * 2
def baseEnd_2425933 : Nat := 830446443069174839787229

theorem tailTrace_2425933 : CollatzResearch.WordTrace tailWord_2425933 prefixEnd_2425933 830446443069174839787229 := by
  unfold tailWord_2425933
  simp only [CollatzResearch.WordTrace]
  refine ⟨88481045520266532216098453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58987363680177688144065635 88481045520266532216098453)
  ·
    refine ⟨4147549008762493697629615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 88481045520266532216098453 4147549008762493697629615)
    ·
      refine ⟨6221323513143740546444423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4147549008762493697629615 6221323513143740546444423)
      ·
        refine ⟨9331985269715610819666635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6221323513143740546444423 9331985269715610819666635)
        ·
          refine ⟨13997977904573416229499953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9331985269715610819666635 13997977904573416229499953)
          ·
            refine ⟨10498483428430062172124965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13997977904573416229499953 10498483428430062172124965)
            ·
              refine ⟨1968465642830636657273431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10498483428430062172124965 1968465642830636657273431)
              ·
                refine ⟨2952698464245954985910147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1968465642830636657273431 2952698464245954985910147)
                ·
                  refine ⟨4429047696368932478865221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2952698464245954985910147 4429047696368932478865221)
                  ·
                    refine ⟨830446443069174839787229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4429047696368932478865221 830446443069174839787229)
                    ·
                      rfl

theorem cell22_2425933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_2425933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425933 prefixEnd_2425933 := by exact prefixLift 2425933
  have htrace : WordTrace (prefixWord ++ tailWord_2425933) baseStart_2425933 baseEnd_2425933 := by
    simpa [prefixWord, tailWord_2425933, baseEnd_2425933] using wordTrace_append hprefix tailTrace_2425933
  have hstable : (prefixWord ++ tailWord_2425933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425933).length < 2 ^ (prefixWord ++ tailWord_2425933).sum := by decide
  have hdescent : baseEnd_2425933 < baseStart_2425933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425974 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 2, 7]
def baseStart_2425974 : Nat := 118140960795 + 2425974 * 2 ^ 59
def prefixEnd_2425974 : Nat := 4983230072969 + 3 ^ 40 * 2425974 * 2
def baseEnd_2425974 : Nat := 830460478207064399512103

theorem tailTrace_2425974 : CollatzResearch.WordTrace tailWord_2425974 prefixEnd_2425974 830460478207064399512103 := by
  unfold tailWord_2425974
  simp only [CollatzResearch.WordTrace]
  refine ⟨5530158807069874763646311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58988360608745330812227317 5530158807069874763646311)
  ·
    refine ⟨8295238210604812145469467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5530158807069874763646311 8295238210604812145469467)
    ·
      refine ⟨12442857315907218218204201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8295238210604812145469467 12442857315907218218204201)
      ·
        refine ⟨9332142986930413663653151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12442857315907218218204201 9332142986930413663653151)
        ·
          refine ⟨13998214480395620495479727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9332142986930413663653151 13998214480395620495479727)
          ·
            refine ⟨20997321720593430743219591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13998214480395620495479727 20997321720593430743219591)
            ·
              refine ⟨31495982580890146114829387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20997321720593430743219591 31495982580890146114829387)
              ·
                refine ⟨47243973871335219172244081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31495982580890146114829387 47243973871335219172244081)
                ·
                  refine ⟨35432980403501414379183061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47243973871335219172244081 35432980403501414379183061)
                  ·
                    refine ⟨830460478207064399512103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35432980403501414379183061 830460478207064399512103)
                    ·
                      rfl

theorem cell22_2425974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_2425974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425974 prefixEnd_2425974 := by exact prefixLift 2425974
  have htrace : WordTrace (prefixWord ++ tailWord_2425974) baseStart_2425974 baseEnd_2425974 := by
    simpa [prefixWord, tailWord_2425974, baseEnd_2425974] using wordTrace_append hprefix tailTrace_2425974
  have hstable : (prefixWord ++ tailWord_2425974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425974).length < 2 ^ (prefixWord ++ tailWord_2425974).sum := by decide
  have hdescent : baseEnd_2425974 < baseStart_2425974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425987 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 9]
def baseStart_2425987 : Nat := 118140960795 + 2425987 * 2 ^ 59
def prefixEnd_2425987 : Nat := 4983230072969 + 3 ^ 40 * 2425987 * 2
def baseEnd_2425987 : Nat := 276821642790912232979021

theorem tailTrace_2425987 : CollatzResearch.WordTrace tailWord_2425987 prefixEnd_2425987 276821642790912232979021 := by
  unfold tailWord_2425987
  simp only [CollatzResearch.WordTrace]
  refine ⟨88483015062070899438564215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58988676708047266292376143 88483015062070899438564215)
  ·
    refine ⟨132724522593106349157846323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88483015062070899438564215 132724522593106349157846323)
    ·
      refine ⟨199086783889659523736769485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132724522593106349157846323 199086783889659523736769485)
      ·
        refine ⟨74657543958622321401288557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199086783889659523736769485 74657543958622321401288557)
        ·
          refine ⟨27996578984483370525483209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74657543958622321401288557 27996578984483370525483209)
          ·
            refine ⟨20997434238362527894112407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27996578984483370525483209 20997434238362527894112407)
            ·
              refine ⟨31496151357543791841168611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20997434238362527894112407 31496151357543791841168611)
              ·
                refine ⟨47244227036315687761752917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31496151357543791841168611 47244227036315687761752917)
                ·
                  refine ⟨276821642790912232979021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47244227036315687761752917 276821642790912232979021)
                  ·
                    rfl

theorem cell22_2425987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 9].length) (baseStart_2425987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2425987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2425987 prefixEnd_2425987 := by exact prefixLift 2425987
  have htrace : WordTrace (prefixWord ++ tailWord_2425987) baseStart_2425987 baseEnd_2425987 := by
    simpa [prefixWord, tailWord_2425987, baseEnd_2425987] using wordTrace_append hprefix tailTrace_2425987
  have hstable : (prefixWord ++ tailWord_2425987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425987).length < 2 ^ (prefixWord ++ tailWord_2425987).sum := by decide
  have hdescent : baseEnd_2425987 < baseStart_2425987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426008 : List Nat := [2, 1, 2, 4, 2, 3, 1, 1, 3, 3]
def baseStart_2426008 : Nat := 118140960795 + 2426008 * 2 ^ 59
def prefixEnd_2426008 : Nat := 4983230072969 + 3 ^ 40 * 2426008 * 2
def baseEnd_2426008 : Nat := 830472117101899644161999

theorem tailTrace_2426008 : CollatzResearch.WordTrace tailWord_2426008 prefixEnd_2426008 830472117101899644161999 := by
  unfold tailWord_2426008
  simp only [CollatzResearch.WordTrace]
  refine ⟨44241890497497410012539339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58989187329996546683385785 44241890497497410012539339)
  ·
    refine ⟨66362835746246115018809009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44241890497497410012539339 66362835746246115018809009)
    ·
      refine ⟨49772126809684586264106757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66362835746246115018809009 49772126809684586264106757)
      ·
        refine ⟨9332273776815859924520017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49772126809684586264106757 9332273776815859924520017)
        ·
          refine ⟨6999205332611894943390013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9332273776815859924520017 6999205332611894943390013)
          ·
            refine ⟨2624701999729460603771255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6999205332611894943390013 2624701999729460603771255)
            ·
              refine ⟨3937052999594190905656883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2624701999729460603771255 3937052999594190905656883)
              ·
                refine ⟨5905579499391286358485325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3937052999594190905656883 5905579499391286358485325)
                ·
                  refine ⟨2214592312271732384431997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5905579499391286358485325 2214592312271732384431997)
                  ·
                    refine ⟨830472117101899644161999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2214592312271732384431997 830472117101899644161999)
                    ·
                      rfl

theorem cell22_2426008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 3, 3].length) (baseStart_2426008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426008 prefixEnd_2426008 := by exact prefixLift 2426008
  have htrace : WordTrace (prefixWord ++ tailWord_2426008) baseStart_2426008 baseEnd_2426008 := by
    simpa [prefixWord, tailWord_2426008, baseEnd_2426008] using wordTrace_append hprefix tailTrace_2426008
  have hstable : (prefixWord ++ tailWord_2426008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426008).length < 2 ^ (prefixWord ++ tailWord_2426008).sum := by decide
  have hdescent : baseEnd_2426008 < baseStart_2426008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426021 : List Nat := [1, 3, 1, 2, 1, 4, 4, 1, 5]
def baseStart_2426021 : Nat := 118140960795 + 2426021 * 2 ^ 59
def prefixEnd_2426021 : Nat := 4983230072969 + 3 ^ 40 * 2426021 * 2
def baseEnd_2426021 : Nat := 276825522422523981195653

theorem tailTrace_2426021 : CollatzResearch.WordTrace tailWord_2426021 prefixEnd_2426021 276825522422523981195653 := by
  unfold tailWord_2426021
  simp only [CollatzResearch.WordTrace]
  refine ⟨88484255143947723245301917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58989503429298482163534611 88484255143947723245301917)
  ·
    refine ⟨33181595678980396216988219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88484255143947723245301917 33181595678980396216988219)
    ·
      refine ⟨49772393518470594325482329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33181595678980396216988219 49772393518470594325482329)
      ·
        refine ⟨37329295138852945744111747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49772393518470594325482329 37329295138852945744111747)
        ·
          refine ⟨55993942708279418616167621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37329295138852945744111747 55993942708279418616167621)
          ·
            refine ⟨10498864257802390990531429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55993942708279418616167621 10498864257802390990531429)
            ·
              refine ⟨1968537048337948310724643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10498864257802390990531429 1968537048337948310724643)
              ·
                refine ⟨2952805572506922466086965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1968537048337948310724643 2952805572506922466086965)
                ·
                  refine ⟨276825522422523981195653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2952805572506922466086965 276825522422523981195653)
                  ·
                    rfl

theorem cell22_2426021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 5].length) (baseStart_2426021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426021 prefixEnd_2426021 := by exact prefixLift 2426021
  have htrace : WordTrace (prefixWord ++ tailWord_2426021) baseStart_2426021 baseEnd_2426021 := by
    simpa [prefixWord, tailWord_2426021, baseEnd_2426021] using wordTrace_append hprefix tailTrace_2426021
  have hstable : (prefixWord ++ tailWord_2426021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426021).length < 2 ^ (prefixWord ++ tailWord_2426021).sum := by decide
  have hdescent : baseEnd_2426021 < baseStart_2426021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426079 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 4, 4]
def baseStart_2426079 : Nat := 118140960795 + 2426079 * 2 ^ 59
def prefixEnd_2426079 : Nat := 4983230072969 + 3 ^ 40 * 2426079 * 2
def baseEnd_2426079 : Nat := 830496421852879125636781

theorem tailTrace_2426079 : CollatzResearch.WordTrace tailWord_2426079 prefixEnd_2426079 830496421852879125636781 := by
  unfold tailWord_2426079
  simp only [CollatzResearch.WordTrace]
  refine ⟨88486370577737599150913291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58990913718491732767275527 88486370577737599150913291)
  ·
    refine ⟨132729555866606398726369937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88486370577737599150913291 132729555866606398726369937)
    ·
      refine ⟨99547166899954799044777453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132729555866606398726369937 99547166899954799044777453)
      ·
        refine ⟨37330187587483049641791545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99547166899954799044777453 37330187587483049641791545)
        ·
          refine ⟨27997640690612287231343659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37330187587483049641791545 27997640690612287231343659)
          ·
            refine ⟨41996461035918430847015489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27997640690612287231343659 41996461035918430847015489)
            ·
              refine ⟨31497345776938823135261617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41996461035918430847015489 31497345776938823135261617)
              ·
                refine ⟨23623009332704117351446213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31497345776938823135261617 23623009332704117351446213)
                ·
                  refine ⟨4429314249882022003396165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23623009332704117351446213 4429314249882022003396165)
                  ·
                    refine ⟨830496421852879125636781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4429314249882022003396165 830496421852879125636781)
                    ·
                      rfl

theorem cell22_2426079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 4].length) (baseStart_2426079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426079 prefixEnd_2426079 := by exact prefixLift 2426079
  have htrace : WordTrace (prefixWord ++ tailWord_2426079) baseStart_2426079 baseEnd_2426079 := by
    simpa [prefixWord, tailWord_2426079, baseEnd_2426079] using wordTrace_append hprefix tailTrace_2426079
  have hstable : (prefixWord ++ tailWord_2426079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426079).length < 2 ^ (prefixWord ++ tailWord_2426079).sum := by decide
  have hdescent : baseEnd_2426079 < baseStart_2426079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426081 : List Nat := [1, 2, 3, 1, 3, 3, 2, 1, 1, 5]
def baseStart_2426081 : Nat := 118140960795 + 2426081 * 2 ^ 59
def prefixEnd_2426081 : Nat := 4983230072969 + 3 ^ 40 * 2426081 * 2
def baseEnd_2426081 : Nat := 830497106493751787086775

theorem tailTrace_2426081 : CollatzResearch.WordTrace tailWord_2426081 prefixEnd_2426081 830497106493751787086775 := by
  unfold tailWord_2426081
  simp only [CollatzResearch.WordTrace]
  refine ⟨88486443523730353492486097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58990962349153568994990731 88486443523730353492486097)
  ·
    refine ⟨66364832642797765119364573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88486443523730353492486097 66364832642797765119364573)
    ·
      refine ⟨24886812241049161919761715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66364832642797765119364573 24886812241049161919761715)
      ·
        refine ⟨37330218361573742879642573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24886812241049161919761715 37330218361573742879642573)
        ·
          refine ⟨13998831885590153579865965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37330218361573742879642573 13998831885590153579865965)
          ·
            refine ⟨5249561957096307592449737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13998831885590153579865965 5249561957096307592449737)
            ·
              refine ⟨3937171467822230694337303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5249561957096307592449737 3937171467822230694337303)
              ·
                refine ⟨5905757201733346041505955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3937171467822230694337303 5905757201733346041505955)
                ·
                  refine ⟨8858635802600019062258933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5905757201733346041505955 8858635802600019062258933)
                  ·
                    refine ⟨830497106493751787086775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8858635802600019062258933 830497106493751787086775)
                    ·
                      rfl

theorem cell22_2426081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_2426081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426081 prefixEnd_2426081 := by exact prefixLift 2426081
  have htrace : WordTrace (prefixWord ++ tailWord_2426081) baseStart_2426081 baseEnd_2426081 := by
    simpa [prefixWord, tailWord_2426081, baseEnd_2426081] using wordTrace_append hprefix tailTrace_2426081
  have hstable : (prefixWord ++ tailWord_2426081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426081).length < 2 ^ (prefixWord ++ tailWord_2426081).sum := by decide
  have hdescent : baseEnd_2426081 < baseStart_2426081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426094 : List Nat := [4, 1, 2, 1, 1, 1, 2, 10]
def baseStart_2426094 : Nat := 118140960795 + 2426094 * 2 ^ 59
def prefixEnd_2426094 : Nat := 4983230072969 + 3 ^ 40 * 2426094 * 2
def baseEnd_2426094 : Nat := 92277950739936009612415

theorem tailTrace_2426094 : CollatzResearch.WordTrace tailWord_2426094 prefixEnd_2426094 92277950739936009612415 := by
  unfold tailWord_2426094
  simp only [CollatzResearch.WordTrace]
  refine ⟨11060864709085407089088667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58991278448455504475139557 11060864709085407089088667)
  ·
    refine ⟨16591297063628110633633001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11060864709085407089088667 16591297063628110633633001)
    ·
      refine ⟨12443472797721082975224751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16591297063628110633633001 12443472797721082975224751)
      ·
        refine ⟨18665209196581624462837127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12443472797721082975224751 18665209196581624462837127)
        ·
          refine ⟨27997813794872436694255691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18665209196581624462837127 27997813794872436694255691)
          ·
            refine ⟨41996720692308655041383537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27997813794872436694255691 41996720692308655041383537)
            ·
              refine ⟨31497540519231491281037653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41996720692308655041383537 31497540519231491281037653)
              ·
                refine ⟨92277950739936009612415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31497540519231491281037653 92277950739936009612415)
                ·
                  rfl

theorem cell22_2426094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 10].length) (baseStart_2426094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426094 prefixEnd_2426094 := by exact prefixLift 2426094
  have htrace : WordTrace (prefixWord ++ tailWord_2426094) baseStart_2426094 baseEnd_2426094 := by
    simpa [prefixWord, tailWord_2426094, baseEnd_2426094] using wordTrace_append hprefix tailTrace_2426094
  have hstable : (prefixWord ++ tailWord_2426094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426094).length < 2 ^ (prefixWord ++ tailWord_2426094).sum := by decide
  have hdescent : baseEnd_2426094 < baseStart_2426094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426220 : List Nat := [2, 2, 1, 1, 5, 2, 3, 1, 1, 4]
def baseStart_2426220 : Nat := 118140960795 + 2426220 * 2 ^ 59
def prefixEnd_2426220 : Nat := 4983230072969 + 3 ^ 40 * 2426220 * 2
def baseEnd_2426220 : Nat := 830544689034401757861349

theorem tailTrace_2426220 : CollatzResearch.WordTrace tailWord_2426220 prefixEnd_2426220 830544689034401757861349 := by
  unfold tailWord_2426220
  simp only [CollatzResearch.WordTrace]
  refine ⟨44245756635113390115898057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58994342180151186821197409 44245756635113390115898057)
  ·
    refine ⟨33184317476335042586923543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44245756635113390115898057 33184317476335042586923543)
    ·
      refine ⟨49776476214502563880385315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33184317476335042586923543 49776476214502563880385315)
      ·
        refine ⟨74664714321753845820577973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49776476214502563880385315 74664714321753845820577973)
        ·
          refine ⟨6999816967664423045679185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74664714321753845820577973 6999816967664423045679185)
          ·
            refine ⟨5249862725748317284259389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6999816967664423045679185 5249862725748317284259389)
            ·
              refine ⟨1968698522155618981597271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5249862725748317284259389 1968698522155618981597271)
              ·
                refine ⟨2953047783233428472395907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1968698522155618981597271 2953047783233428472395907)
                ·
                  refine ⟨4429571674850142708593861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2953047783233428472395907 4429571674850142708593861)
                  ·
                    refine ⟨830544689034401757861349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4429571674850142708593861 830544689034401757861349)
                    ·
                      rfl

theorem cell22_2426220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 4].length) (baseStart_2426220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426220 prefixEnd_2426220 := by exact prefixLift 2426220
  have htrace : WordTrace (prefixWord ++ tailWord_2426220) baseStart_2426220 baseEnd_2426220 := by
    simpa [prefixWord, tailWord_2426220, baseEnd_2426220] using wordTrace_append hprefix tailTrace_2426220
  have hstable : (prefixWord ++ tailWord_2426220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426220).length < 2 ^ (prefixWord ++ tailWord_2426220).sum := by decide
  have hdescent : baseEnd_2426220 < baseStart_2426220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426231 : List Nat := [1, 1, 3, 1, 1, 2, 3, 4, 2, 4]
def baseStart_2426231 : Nat := 118140960795 + 2426231 * 2 ^ 59
def prefixEnd_2426231 : Nat := 4983230072969 + 3 ^ 40 * 2426231 * 2
def baseEnd_2426231 : Nat := 830548454559201395836315

theorem tailTrace_2426231 : CollatzResearch.WordTrace tailWord_2426231 prefixEnd_2426231 830548454559201395836315 := by
  unfold tailWord_2426231
  simp only [CollatzResearch.WordTrace]
  refine ⟨88491914473186929110446547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58994609648791286073631031 88491914473186929110446547)
  ·
    refine ⟨132737871709780393665669821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88491914473186929110446547 132737871709780393665669821)
    ·
      refine ⟨49776701891167647624626183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132737871709780393665669821 49776701891167647624626183)
      ·
        refine ⟨74665052836751471436939275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49776701891167647624626183 74665052836751471436939275)
        ·
          refine ⟨111997579255127207155408913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74665052836751471436939275 111997579255127207155408913)
          ·
            refine ⟨83998184441345405366556685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111997579255127207155408913 83998184441345405366556685)
            ·
              refine ⟨31499319165504527012458757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83998184441345405366556685 31499319165504527012458757)
              ·
                refine ⟨5906122343532098814836017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31499319165504527012458757 5906122343532098814836017)
                ·
                  refine ⟨4429591757649074111127013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5906122343532098814836017 4429591757649074111127013)
                  ·
                    refine ⟨830548454559201395836315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4429591757649074111127013 830548454559201395836315)
                    ·
                      rfl

theorem cell22_2426231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_2426231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426231 prefixEnd_2426231 := by exact prefixLift 2426231
  have htrace : WordTrace (prefixWord ++ tailWord_2426231) baseStart_2426231 baseEnd_2426231 := by
    simpa [prefixWord, tailWord_2426231, baseEnd_2426231] using wordTrace_append hprefix tailTrace_2426231
  have hstable : (prefixWord ++ tailWord_2426231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426231).length < 2 ^ (prefixWord ++ tailWord_2426231).sum := by decide
  have hdescent : baseEnd_2426231 < baseStart_2426231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426233 : List Nat := [1, 2, 1, 3, 2, 1, 3, 4, 2, 3]
def baseStart_2426233 : Nat := 118140960795 + 2426233 * 2 ^ 59
def prefixEnd_2426233 : Nat := 4983230072969 + 3 ^ 40 * 2426233 * 2
def baseEnd_2426233 : Nat := 830549139200074057286309

theorem tailTrace_2426233 : CollatzResearch.WordTrace tailWord_2426233 prefixEnd_2426233 830549139200074057286309 := by
  unfold tailWord_2426233
  simp only [CollatzResearch.WordTrace]
  refine ⟨88491987419179683452019353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58994658279453122301346235 88491987419179683452019353)
  ·
    refine ⟨66368990564384762589014515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88491987419179683452019353 66368990564384762589014515)
    ·
      refine ⟨99553485846577143883521773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66368990564384762589014515 99553485846577143883521773)
      ·
        refine ⟨37332557192466428956320665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99553485846577143883521773 37332557192466428956320665)
        ·
          refine ⟨27999417894349821717240499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37332557192466428956320665 27999417894349821717240499)
          ·
            refine ⟨41999126841524732575860749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27999417894349821717240499 41999126841524732575860749)
            ·
              refine ⟨15749672565571774715947781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41999126841524732575860749 15749672565571774715947781)
              ·
                refine ⟨2953063606044707759240209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15749672565571774715947781 2953063606044707759240209)
                ·
                  refine ⟨2214797704533530819430157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2953063606044707759240209 2214797704533530819430157)
                  ·
                    refine ⟨830549139200074057286309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2214797704533530819430157 830549139200074057286309)
                    ·
                      rfl

theorem cell22_2426233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 2, 3].length) (baseStart_2426233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426233 prefixEnd_2426233 := by exact prefixLift 2426233
  have htrace : WordTrace (prefixWord ++ tailWord_2426233) baseStart_2426233 baseEnd_2426233 := by
    simpa [prefixWord, tailWord_2426233, baseEnd_2426233] using wordTrace_append hprefix tailTrace_2426233
  have hstable : (prefixWord ++ tailWord_2426233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426233).length < 2 ^ (prefixWord ++ tailWord_2426233).sum := by decide
  have hdescent : baseEnd_2426233 < baseStart_2426233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426295 : List Nat := [1, 1, 3, 1, 3, 2, 1, 6, 1, 3]
def baseStart_2426295 : Nat := 118140960795 + 2426295 * 2 ^ 59
def prefixEnd_2426295 : Nat := 4983230072969 + 3 ^ 40 * 2426295 * 2
def baseEnd_2426295 : Nat := 830570363067126562236119

theorem tailTrace_2426295 : CollatzResearch.WordTrace tailWord_2426295 prefixEnd_2426295 830570363067126562236119 := by
  unfold tailWord_2426295
  simp only [CollatzResearch.WordTrace]
  refine ⟨88494248744955068040776339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58996165829970045360517559 88494248744955068040776339)
  ·
    refine ⟨132741373117432602061164509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88494248744955068040776339 132741373117432602061164509)
    ·
      refine ⟨49778014919037225772936691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132741373117432602061164509 49778014919037225772936691)
      ·
        refine ⟨74667022378555838659405037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49778014919037225772936691 74667022378555838659405037)
        ·
          refine ⟨28000133391958439497276889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74667022378555838659405037 28000133391958439497276889)
          ·
            refine ⟨21000100043968829622957667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28000133391958439497276889 21000100043968829622957667)
            ·
              refine ⟨31500150065953244434436501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21000100043968829622957667 31500150065953244434436501)
              ·
                refine ⟨1476569534341558332864211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31500150065953244434436501 1476569534341558332864211)
                ·
                  refine ⟨2214854301512337499296317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1476569534341558332864211 2214854301512337499296317)
                  ·
                    refine ⟨830570363067126562236119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2214854301512337499296317 830570363067126562236119)
                    ·
                      rfl

theorem cell22_2426295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 6, 1, 3].length) (baseStart_2426295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426295 prefixEnd_2426295 := by exact prefixLift 2426295
  have htrace : WordTrace (prefixWord ++ tailWord_2426295) baseStart_2426295 baseEnd_2426295 := by
    simpa [prefixWord, tailWord_2426295, baseEnd_2426295] using wordTrace_append hprefix tailTrace_2426295
  have hstable : (prefixWord ++ tailWord_2426295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426295).length < 2 ^ (prefixWord ++ tailWord_2426295).sum := by decide
  have hdescent : baseEnd_2426295 < baseStart_2426295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426353 : List Nat := [1, 2, 2, 2, 3, 2, 3, 1, 6]
def baseStart_2426353 : Nat := 118140960795 + 2426353 * 2 ^ 59
def prefixEnd_2426353 : Nat := 4983230072969 + 3 ^ 40 * 2426353 * 2
def baseEnd_2426353 : Nat := 276863405884144581428647

theorem tailTrace_2426353 : CollatzResearch.WordTrace tailWord_2426353 prefixEnd_2426353 276863405884144581428647 := by
  unfold tailWord_2426353
  simp only [CollatzResearch.WordTrace]
  refine ⟨88496364178744943946387713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58997576119163295964258475 88496364178744943946387713)
  ·
    refine ⟨66372273134058707959790785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88496364178744943946387713 66372273134058707959790785)
    ·
      refine ⟨49779204850544030969843089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66372273134058707959790785 49779204850544030969843089)
      ·
        refine ⟨37334403637908023227382317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49779204850544030969843089 37334403637908023227382317)
        ·
          refine ⟨14000401364215508710268369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37334403637908023227382317 14000401364215508710268369)
          ·
            refine ⟨10500301023161631532701277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14000401364215508710268369 10500301023161631532701277)
            ·
              refine ⟨3937612883685611824762979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10500301023161631532701277 3937612883685611824762979)
              ·
                refine ⟨5906419325528417737144469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3937612883685611824762979 5906419325528417737144469)
                ·
                  refine ⟨276863405884144581428647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5906419325528417737144469 276863405884144581428647)
                  ·
                    rfl

theorem cell22_2426353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 6].length) (baseStart_2426353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426353 prefixEnd_2426353 := by exact prefixLift 2426353
  have htrace : WordTrace (prefixWord ++ tailWord_2426353) baseStart_2426353 baseEnd_2426353 := by
    simpa [prefixWord, tailWord_2426353, baseEnd_2426353] using wordTrace_append hprefix tailTrace_2426353
  have hstable : (prefixWord ++ tailWord_2426353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426353).length < 2 ^ (prefixWord ++ tailWord_2426353).sum := by decide
  have hdescent : baseEnd_2426353 < baseStart_2426353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426400 : List Nat := [2, 1, 1, 6, 1, 1, 2, 2, 2, 4]
def baseStart_2426400 : Nat := 118140960795 + 2426400 * 2 ^ 59
def prefixEnd_2426400 : Nat := 4983230072969 + 3 ^ 40 * 2426400 * 2
def baseEnd_2426400 : Nat := 830606306712941288360797

theorem tailTrace_2426400 : CollatzResearch.WordTrace tailWord_2426400 prefixEnd_2426400 830606306712941288360797 := by
  unfold tailWord_2426400
  simp only [CollatzResearch.WordTrace]
  refine ⟨44249039204787335486674327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58998718939716447315565769 44249039204787335486674327)
  ·
    refine ⟨66373558807181003230011491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44249039204787335486674327 66373558807181003230011491)
    ·
      refine ⟨99560338210771504845017237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66373558807181003230011491 99560338210771504845017237)
      ·
        refine ⟨4666890853629914289610183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 99560338210771504845017237 4666890853629914289610183)
        ·
          refine ⟨7000336280444871434415275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4666890853629914289610183 7000336280444871434415275)
          ·
            refine ⟨10500504420667307151622913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7000336280444871434415275 10500504420667307151622913)
            ·
              refine ⟨7875378315500480363717185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10500504420667307151622913 7875378315500480363717185)
              ·
                refine ⟨5906533736625360272787889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7875378315500480363717185 5906533736625360272787889)
                ·
                  refine ⟨4429900302469020204590917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5906533736625360272787889 4429900302469020204590917)
                  ·
                    refine ⟨830606306712941288360797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4429900302469020204590917 830606306712941288360797)
                    ·
                      rfl

theorem cell22_2426400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 2, 4].length) (baseStart_2426400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426400 prefixEnd_2426400 := by exact prefixLift 2426400
  have htrace : WordTrace (prefixWord ++ tailWord_2426400) baseStart_2426400 baseEnd_2426400 := by
    simpa [prefixWord, tailWord_2426400, baseEnd_2426400] using wordTrace_append hprefix tailTrace_2426400
  have hstable : (prefixWord ++ tailWord_2426400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426400).length < 2 ^ (prefixWord ++ tailWord_2426400).sum := by decide
  have hdescent : baseEnd_2426400 < baseStart_2426400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426460 : List Nat := [2, 2, 4, 1, 2, 2, 1, 1, 7]
def baseStart_2426460 : Nat := 118140960795 + 2426460 * 2 ^ 59
def prefixEnd_2426460 : Nat := 4983230072969 + 3 ^ 40 * 2426460 * 2
def baseEnd_2426460 : Nat := 276875615313040377286871

theorem tailTrace_2426460 : CollatzResearch.WordTrace tailWord_2426460 prefixEnd_2426460 276875615313040377286871 := by
  unfold tailWord_2426460
  simp only [CollatzResearch.WordTrace]
  refine ⟨44250133394678650610266417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59000177859571534147021889 44250133394678650610266417)
  ·
    refine ⟨33187600046008987957699813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44250133394678650610266417 33187600046008987957699813)
    ·
      refine ⟨6222675008626685242068715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33187600046008987957699813 6222675008626685242068715)
      ·
        refine ⟨9334012512940027863103073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6222675008626685242068715 9334012512940027863103073)
        ·
          refine ⟨7000509384705020897327305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9334012512940027863103073 7000509384705020897327305)
          ·
            refine ⟨5250382038528765672995479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7000509384705020897327305 5250382038528765672995479)
            ·
              refine ⟨7875573057793148509493219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5250382038528765672995479 7875573057793148509493219)
              ·
                refine ⟨11813359586689722764239829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7875573057793148509493219 11813359586689722764239829)
                ·
                  refine ⟨276875615313040377286871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11813359586689722764239829 276875615313040377286871)
                  ·
                    rfl

theorem cell22_2426460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 7].length) (baseStart_2426460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426460 prefixEnd_2426460 := by exact prefixLift 2426460
  have htrace : WordTrace (prefixWord ++ tailWord_2426460) baseStart_2426460 baseEnd_2426460 := by
    simpa [prefixWord, tailWord_2426460, baseEnd_2426460] using wordTrace_append hprefix tailTrace_2426460
  have hstable : (prefixWord ++ tailWord_2426460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426460).length < 2 ^ (prefixWord ++ tailWord_2426460).sum := by decide
  have hdescent : baseEnd_2426460 < baseStart_2426460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426473 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 5, 4]
def baseStart_2426473 : Nat := 118140960795 + 2426473 * 2 ^ 59
def prefixEnd_2426473 : Nat := 4983230072969 + 3 ^ 40 * 2426473 * 2
def baseEnd_2426473 : Nat := 830631296104793431285573

theorem tailTrace_2426473 : CollatzResearch.WordTrace tailWord_2426473 prefixEnd_2426473 830631296104793431285573 := by
  unfold tailWord_2426473
  simp only [CollatzResearch.WordTrace]
  refine ⟨88500740938310204440756073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59000493958873469627170715 88500740938310204440756073)
  ·
    refine ⟨66375555703732653330567055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88500740938310204440756073 66375555703732653330567055)
    ·
      refine ⟨99563333555598979995850583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66375555703732653330567055 99563333555598979995850583)
      ·
        refine ⟨149345000333398469993775875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99563333555598979995850583 149345000333398469993775875)
        ·
          refine ⟨224017500500097704990663813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149345000333398469993775875 224017500500097704990663813)
          ·
            refine ⟨42003281343768319685749465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 224017500500097704990663813 42003281343768319685749465)
            ·
              refine ⟨31502461007826239764312099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42003281343768319685749465 31502461007826239764312099)
              ·
                refine ⟨47253691511739359646468149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31502461007826239764312099 47253691511739359646468149)
                ·
                  refine ⟨4430033579225564966856389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47253691511739359646468149 4430033579225564966856389)
                  ·
                    refine ⟨830631296104793431285573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4430033579225564966856389 830631296104793431285573)
                    ·
                      rfl

theorem cell22_2426473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 4].length) (baseStart_2426473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426473 prefixEnd_2426473 := by exact prefixLift 2426473
  have htrace : WordTrace (prefixWord ++ tailWord_2426473) baseStart_2426473 baseEnd_2426473 := by
    simpa [prefixWord, tailWord_2426473, baseEnd_2426473] using wordTrace_append hprefix tailTrace_2426473
  have hstable : (prefixWord ++ tailWord_2426473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426473).length < 2 ^ (prefixWord ++ tailWord_2426473).sum := by decide
  have hdescent : baseEnd_2426473 < baseStart_2426473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426533 : List Nat := [1, 3, 1, 2, 1, 2, 3, 9]
def baseStart_2426533 : Nat := 118140960795 + 2426533 * 2 ^ 59
def prefixEnd_2426533 : Nat := 4983230072969 + 3 ^ 40 * 2426533 * 2
def baseEnd_2426533 : Nat := 92294648370108141642821

theorem tailTrace_2426533 : CollatzResearch.WordTrace tailWord_2426533 prefixEnd_2426533 92294648370108141642821 := by
  unfold tailWord_2426533
  simp only [CollatzResearch.WordTrace]
  refine ⟨88502929318092834687940253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59001952878728556458626835 88502929318092834687940253)
  ·
    refine ⟨33188598494284813007977595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88502929318092834687940253 33188598494284813007977595)
    ·
      refine ⟨49782897741427219511966393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33188598494284813007977595 49782897741427219511966393)
      ·
        refine ⟨37337173306070414633974795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49782897741427219511966393 37337173306070414633974795)
        ·
          refine ⟨56005759959105621950962193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37337173306070414633974795 56005759959105621950962193)
          ·
            refine ⟨42004319969329216463221645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56005759959105621950962193 42004319969329216463221645)
            ·
              refine ⟨15751619988498456173708117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42004319969329216463221645 15751619988498456173708117)
              ·
                refine ⟨92294648370108141642821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15751619988498456173708117 92294648370108141642821)
                ·
                  rfl

theorem cell22_2426533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 9].length) (baseStart_2426533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426533 prefixEnd_2426533 := by exact prefixLift 2426533
  have htrace : WordTrace (prefixWord ++ tailWord_2426533) baseStart_2426533 baseEnd_2426533 := by
    simpa [prefixWord, tailWord_2426533, baseEnd_2426533] using wordTrace_append hprefix tailTrace_2426533
  have hstable : (prefixWord ++ tailWord_2426533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426533).length < 2 ^ (prefixWord ++ tailWord_2426533).sum := by decide
  have hdescent : baseEnd_2426533 < baseStart_2426533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426563 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 6, 6]
def baseStart_2426563 : Nat := 118140960795 + 2426563 * 2 ^ 59
def prefixEnd_2426563 : Nat := 4983230072969 + 3 ^ 40 * 2426563 * 2
def baseEnd_2426563 : Nat := 830662104944063196535297

theorem tailTrace_2426563 : CollatzResearch.WordTrace tailWord_2426563 prefixEnd_2426563 830662104944063196535297 := by
  unfold tailWord_2426563
  simp only [CollatzResearch.WordTrace]
  refine ⟨88504023507984149811532343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59002682338656099874354895 88504023507984149811532343)
  ·
    refine ⟨132756035261976224717298515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88504023507984149811532343 132756035261976224717298515)
    ·
      refine ⟨199134052892964337075947773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132756035261976224717298515 199134052892964337075947773)
      ·
        refine ⟨74675269834861626403480415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199134052892964337075947773 74675269834861626403480415)
        ·
          refine ⟨112012904752292439605220623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74675269834861626403480415 112012904752292439605220623)
          ·
            refine ⟨168019357128438659407830935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112012904752292439605220623 168019357128438659407830935)
            ·
              refine ⟨252029035692657989111746403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168019357128438659407830935 252029035692657989111746403)
              ·
                refine ⟨378043553538986983667619605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252029035692657989111746403 378043553538986983667619605)
                ·
                  refine ⟨17720791572140014859419669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 378043553538986983667619605 17720791572140014859419669)
                  ·
                    refine ⟨830662104944063196535297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17720791572140014859419669 830662104944063196535297)
                    ·
                      rfl

theorem cell22_2426563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 6].length) (baseStart_2426563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426563 prefixEnd_2426563 := by exact prefixLift 2426563
  have htrace : WordTrace (prefixWord ++ tailWord_2426563) baseStart_2426563 baseEnd_2426563 := by
    simpa [prefixWord, tailWord_2426563, baseEnd_2426563] using wordTrace_append hprefix tailTrace_2426563
  have hstable : (prefixWord ++ tailWord_2426563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426563).length < 2 ^ (prefixWord ++ tailWord_2426563).sum := by decide
  have hdescent : baseEnd_2426563 < baseStart_2426563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426565 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 5, 3]
def baseStart_2426565 : Nat := 118140960795 + 2426565 * 2 ^ 59
def prefixEnd_2426565 : Nat := 4983230072969 + 3 ^ 40 * 2426565 * 2
def baseEnd_2426565 : Nat := 830662789584935857985291

theorem tailTrace_2426565 : CollatzResearch.WordTrace tailWord_2426565 prefixEnd_2426565 830662789584935857985291 := by
  unfold tailWord_2426565
  simp only [CollatzResearch.WordTrace]
  refine ⟨88504096453976904153105149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59002730969317936102070099 88504096453976904153105149)
  ·
    refine ⟨33189036170241339057414431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88504096453976904153105149 33189036170241339057414431)
    ·
      refine ⟨49783554255362008586121647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33189036170241339057414431 49783554255362008586121647)
      ·
        refine ⟨74675331383043012879182471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49783554255362008586121647 74675331383043012879182471)
        ·
          refine ⟨112012997074564519318773707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74675331383043012879182471 112012997074564519318773707)
          ·
            refine ⟨168019495611846778978160561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112012997074564519318773707 168019495611846778978160561)
            ·
              refine ⟨126014621708885084233620421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168019495611846778978160561 126014621708885084233620421)
              ·
                refine ⟨23627741570415953293803829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126014621708885084233620421 23627741570415953293803829)
                ·
                  refine ⟨2215100772226495621294109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23627741570415953293803829 2215100772226495621294109)
                  ·
                    refine ⟨830662789584935857985291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2215100772226495621294109 830662789584935857985291)
                    ·
                      rfl

theorem cell22_2426565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 5, 3].length) (baseStart_2426565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426565 prefixEnd_2426565 := by exact prefixLift 2426565
  have htrace : WordTrace (prefixWord ++ tailWord_2426565) baseStart_2426565 baseEnd_2426565 := by
    simpa [prefixWord, tailWord_2426565, baseEnd_2426565] using wordTrace_append hprefix tailTrace_2426565
  have hstable : (prefixWord ++ tailWord_2426565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426565).length < 2 ^ (prefixWord ++ tailWord_2426565).sum := by decide
  have hdescent : baseEnd_2426565 < baseStart_2426565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426573 : List Nat := [1, 6, 2, 1, 1, 3, 2, 2, 4]
def baseStart_2426573 : Nat := 118140960795 + 2426573 * 2 ^ 59
def prefixEnd_2426573 : Nat := 4983230072969 + 3 ^ 40 * 2426573 * 2
def baseEnd_2426573 : Nat := 276888509382808834595089

theorem tailTrace_2426573 : CollatzResearch.WordTrace tailWord_2426573 prefixEnd_2426573 276888509382808834595089 := by
  unfold tailWord_2426573
  simp only [CollatzResearch.WordTrace]
  refine ⟨88504388237947921519396373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59002925491965281012930915 88504388237947921519396373)
  ·
    refine ⟨4148643198653808821221705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 88504388237947921519396373 4148643198653808821221705)
    ·
      refine ⟨3111482398990356615916279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4148643198653808821221705 3111482398990356615916279)
      ·
        refine ⟨4667223598485534923874419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3111482398990356615916279 4667223598485534923874419)
        ·
          refine ⟨7000835397728302385811629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4667223598485534923874419 7000835397728302385811629)
          ·
            refine ⟨2625313274148113394679361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7000835397728302385811629 2625313274148113394679361)
            ·
              refine ⟨1968984955611085046009521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2625313274148113394679361 1968984955611085046009521)
              ·
                refine ⟨1476738716708313784507141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1968984955611085046009521 1476738716708313784507141)
                ·
                  refine ⟨276888509382808834595089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1476738716708313784507141 276888509382808834595089)
                  ·
                    rfl

theorem cell22_2426573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_2426573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426573 prefixEnd_2426573 := by exact prefixLift 2426573
  have htrace : WordTrace (prefixWord ++ tailWord_2426573) baseStart_2426573 baseEnd_2426573 := by
    simpa [prefixWord, tailWord_2426573, baseEnd_2426573] using wordTrace_append hprefix tailTrace_2426573
  have hstable : (prefixWord ++ tailWord_2426573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426573).length < 2 ^ (prefixWord ++ tailWord_2426573).sum := by decide
  have hdescent : baseEnd_2426573 < baseStart_2426573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426610 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 1, 7]
def baseStart_2426610 : Nat := 118140960795 + 2426610 * 2 ^ 59
def prefixEnd_2426610 : Nat := 4983230072969 + 3 ^ 40 * 2426610 * 2
def baseEnd_2426610 : Nat := 830678194004570740610153

theorem tailTrace_2426610 : CollatzResearch.WordTrace tailWord_2426610 prefixEnd_2426610 830678194004570740610153 := by
  unfold tailWord_2426610
  simp only [CollatzResearch.WordTrace]
  refine ⟨22126434434703469209623321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59003825159209251225662189 22126434434703469209623321)
  ·
    refine ⟨16594825826027601907217491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22126434434703469209623321 16594825826027601907217491)
    ·
      refine ⟨24892238739041402860826237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16594825826027601907217491 24892238739041402860826237)
      ·
        refine ⟨9334589527140526072809839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24892238739041402860826237 9334589527140526072809839)
        ·
          refine ⟨14001884290710789109214759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9334589527140526072809839 14001884290710789109214759)
          ·
            refine ⟨21002826436066183663822139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14001884290710789109214759 21002826436066183663822139)
            ·
              refine ⟨31504239654099275495733209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21002826436066183663822139 31504239654099275495733209)
              ·
                refine ⟨23628179740574456621799907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31504239654099275495733209 23628179740574456621799907)
                ·
                  refine ⟨35442269610861684932699861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23628179740574456621799907 35442269610861684932699861)
                  ·
                    refine ⟨830678194004570740610153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35442269610861684932699861 830678194004570740610153)
                    ·
                      rfl

theorem cell22_2426610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_2426610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426610 prefixEnd_2426610 := by exact prefixLift 2426610
  have htrace : WordTrace (prefixWord ++ tailWord_2426610) baseStart_2426610 baseEnd_2426610 := by
    simpa [prefixWord, tailWord_2426610, baseEnd_2426610] using wordTrace_append hprefix tailTrace_2426610
  have hstable : (prefixWord ++ tailWord_2426610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426610).length < 2 ^ (prefixWord ++ tailWord_2426610).sum := by decide
  have hdescent : baseEnd_2426610 < baseStart_2426610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426674 : List Nat := [3, 2, 1, 1, 3, 2, 3, 3, 4]
def baseStart_2426674 : Nat := 118140960795 + 2426674 * 2 ^ 59
def prefixEnd_2426674 : Nat := 4983230072969 + 3 ^ 40 * 2426674 * 2
def baseEnd_2426674 : Nat := 276900034170831969003319

theorem tailTrace_2426674 : CollatzResearch.WordTrace tailWord_2426674 prefixEnd_2426674 276900034170831969003319 := by
  unfold tailWord_2426674
  simp only [CollatzResearch.WordTrace]
  refine ⟨22127018002645503942205769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59005381340388010512548717 22127018002645503942205769)
  ·
    refine ⟨16595263501984127956654327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22127018002645503942205769 16595263501984127956654327)
    ·
      refine ⟨24892895252976191934981491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16595263501984127956654327 24892895252976191934981491)
      ·
        refine ⟨37339342879464287902472237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24892895252976191934981491 37339342879464287902472237)
        ·
          refine ⟨14002253579799107963427089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37339342879464287902472237 14002253579799107963427089)
          ·
            refine ⟨10501690184849330972570317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14002253579799107963427089 10501690184849330972570317)
            ·
              refine ⟨3938133819318499114713869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10501690184849330972570317 3938133819318499114713869)
              ·
                refine ⟨1476800182244437168017701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3938133819318499114713869 1476800182244437168017701)
                ·
                  refine ⟨276900034170831969003319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1476800182244437168017701 276900034170831969003319)
                  ·
                    rfl

theorem cell22_2426674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_2426674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426674 prefixEnd_2426674 := by exact prefixLift 2426674
  have htrace : WordTrace (prefixWord ++ tailWord_2426674) baseStart_2426674 baseEnd_2426674 := by
    simpa [prefixWord, tailWord_2426674, baseEnd_2426674] using wordTrace_append hprefix tailTrace_2426674
  have hstable : (prefixWord ++ tailWord_2426674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426674).length < 2 ^ (prefixWord ++ tailWord_2426674).sum := by decide
  have hdescent : baseEnd_2426674 < baseStart_2426674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426706 : List Nat := [3, 2, 2, 1, 1, 3, 4, 1, 2, 3]
def baseStart_2426706 : Nat := 118140960795 + 2426706 * 2 ^ 59
def prefixEnd_2426706 : Nat := 4983230072969 + 3 ^ 40 * 2426706 * 2
def baseEnd_2426706 : Nat := 830711056766458490209859

theorem tailTrace_2426706 : CollatzResearch.WordTrace tailWord_2426706 prefixEnd_2426706 830711056766458490209859 := by
  unfold tailWord_2426706
  simp only [CollatzResearch.WordTrace]
  refine ⟨22127309786616521308496993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59006159430977390155991981 22127309786616521308496993)
  ·
    refine ⟨16595482339962390981372745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22127309786616521308496993 16595482339962390981372745)
    ·
      refine ⟨12446611754971793236029559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16595482339962390981372745 12446611754971793236029559)
      ·
        refine ⟨18669917632457689854044339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12446611754971793236029559 18669917632457689854044339)
        ·
          refine ⟨28004876448686534781066509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18669917632457689854044339 28004876448686534781066509)
          ·
            refine ⟨10501828668257450542899941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28004876448686534781066509 10501828668257450542899941)
            ·
              refine ⟨1969092875298271976793739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10501828668257450542899941 1969092875298271976793739)
              ·
                refine ⟨2953639312947407965190609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1969092875298271976793739 2953639312947407965190609)
                ·
                  refine ⟨2215229484710555973892957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2953639312947407965190609 2215229484710555973892957)
                  ·
                    refine ⟨830711056766458490209859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2215229484710555973892957 830711056766458490209859)
                    ·
                      rfl

theorem cell22_2426706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_2426706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426706 prefixEnd_2426706 := by exact prefixLift 2426706
  have htrace : WordTrace (prefixWord ++ tailWord_2426706) baseStart_2426706 baseEnd_2426706 := by
    simpa [prefixWord, tailWord_2426706, baseEnd_2426706] using wordTrace_append hprefix tailTrace_2426706
  have hstable : (prefixWord ++ tailWord_2426706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426706).length < 2 ^ (prefixWord ++ tailWord_2426706).sum := by decide
  have hdescent : baseEnd_2426706 < baseStart_2426706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426777 : List Nat := [1, 2, 1, 2, 1, 3, 4, 1, 3, 4]
def baseStart_2426777 : Nat := 118140960795 + 2426777 * 2 ^ 59
def prefixEnd_2426777 : Nat := 4983230072969 + 3 ^ 40 * 2426777 * 2
def baseEnd_2426777 : Nat := 830735361517437971684641

theorem tailTrace_2426777 : CollatzResearch.WordTrace tailWord_2426777 prefixEnd_2426777 830735361517437971684641 := by
  unfold tailWord_2426777
  simp only [CollatzResearch.WordTrace]
  refine ⟨88511828729208864359822585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59007885819472576239881723 88511828729208864359822585)
  ·
    refine ⟨66383871546906648269866939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88511828729208864359822585 66383871546906648269866939)
    ·
      refine ⟨99575807320359972404800409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66383871546906648269866939 99575807320359972404800409)
      ·
        refine ⟨74681855490269979303600307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99575807320359972404800409 74681855490269979303600307)
        ·
          refine ⟨112022783235404968955400461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74681855490269979303600307 112022783235404968955400461)
          ·
            refine ⟨42008543713276863358275173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112022783235404968955400461 42008543713276863358275173)
            ·
              refine ⟨7876601946239411879676595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42008543713276863358275173 7876601946239411879676595)
              ·
                refine ⟨11814902919359117819514893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7876601946239411879676595 11814902919359117819514893)
                ·
                  refine ⟨4430588594759669182318085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11814902919359117819514893 4430588594759669182318085)
                  ·
                    refine ⟨830735361517437971684641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4430588594759669182318085 830735361517437971684641)
                    ·
                      rfl

theorem cell22_2426777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 4].length) (baseStart_2426777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426777 prefixEnd_2426777 := by exact prefixLift 2426777
  have htrace : WordTrace (prefixWord ++ tailWord_2426777) baseStart_2426777 baseEnd_2426777 := by
    simpa [prefixWord, tailWord_2426777, baseEnd_2426777] using wordTrace_append hprefix tailTrace_2426777
  have hstable : (prefixWord ++ tailWord_2426777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426777).length < 2 ^ (prefixWord ++ tailWord_2426777).sum := by decide
  have hdescent : baseEnd_2426777 < baseStart_2426777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426798 : List Nat := [4, 1, 5, 1, 1, 1, 1, 1, 7]
def baseStart_2426798 : Nat := 118140960795 + 2426798 * 2 ^ 59
def prefixEnd_2426798 : Nat := 4983230072969 + 3 ^ 40 * 2426798 * 2
def baseEnd_2426798 : Nat := 276914183415533638969859

theorem tailTrace_2426798 : CollatzResearch.WordTrace tailWord_2426798 prefixEnd_2426798 276914183415533638969859 := by
  unfold tailWord_2426798
  simp only [CollatzResearch.WordTrace]
  refine ⟨11064074332766598118292131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59008396441421856630891365 11064074332766598118292131)
  ·
    refine ⟨16596111499149897177438197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11064074332766598118292131 16596111499149897177438197)
    ·
      refine ⟨1555885453045302860384831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16596111499149897177438197 1555885453045302860384831)
      ·
        refine ⟨2333828179567954290577247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1555885453045302860384831 2333828179567954290577247)
        ·
          refine ⟨3500742269351931435865871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2333828179567954290577247 3500742269351931435865871)
          ·
            refine ⟨5251113404027897153798807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3500742269351931435865871 5251113404027897153798807)
            ·
              refine ⟨7876670106041845730698211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5251113404027897153798807 7876670106041845730698211)
              ·
                refine ⟨11815005159062768596047317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7876670106041845730698211 11815005159062768596047317)
                ·
                  refine ⟨276914183415533638969859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11815005159062768596047317 276914183415533638969859)
                  ·
                    rfl

theorem cell22_2426798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_2426798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426798 prefixEnd_2426798 := by exact prefixLift 2426798
  have htrace : WordTrace (prefixWord ++ tailWord_2426798) baseStart_2426798 baseEnd_2426798 := by
    simpa [prefixWord, tailWord_2426798, baseEnd_2426798] using wordTrace_append hprefix tailTrace_2426798
  have hstable : (prefixWord ++ tailWord_2426798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426798).length < 2 ^ (prefixWord ++ tailWord_2426798).sum := by decide
  have hdescent : baseEnd_2426798 < baseStart_2426798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426809 : List Nat := [1, 2, 1, 4, 2, 1, 1, 6, 4]
def baseStart_2426809 : Nat := 118140960795 + 2426809 * 2 ^ 59
def prefixEnd_2426809 : Nat := 4983230072969 + 3 ^ 40 * 2426809 * 2
def baseEnd_2426809 : Nat := 276915438590466851628181

theorem tailTrace_2426809 : CollatzResearch.WordTrace tailWord_2426809 prefixEnd_2426809 276915438590466851628181 := by
  unfold tailWord_2426809
  simp only [CollatzResearch.WordTrace]
  refine ⟨88512995865092933824987481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59008663910061955883324987 88512995865092933824987481)
  ·
    refine ⟨66384746898819700368740611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88512995865092933824987481 66384746898819700368740611)
    ·
      refine ⟨99577120348229550553110917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66384746898819700368740611 99577120348229550553110917)
      ·
        refine ⟨18670710065293040728708297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99577120348229550553110917 18670710065293040728708297)
        ·
          refine ⟨14003032548969780546531223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18670710065293040728708297 14003032548969780546531223)
          ·
            refine ⟨21004548823454670819796835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14003032548969780546531223 21004548823454670819796835)
            ·
              refine ⟨31506823235182006229695253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21004548823454670819796835 31506823235182006229695253)
              ·
                refine ⟨1476882339149156542016965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31506823235182006229695253 1476882339149156542016965)
                ·
                  refine ⟨276915438590466851628181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1476882339149156542016965 276915438590466851628181)
                  ·
                    rfl

theorem cell22_2426809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 6, 4].length) (baseStart_2426809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426809 prefixEnd_2426809 := by exact prefixLift 2426809
  have htrace : WordTrace (prefixWord ++ tailWord_2426809) baseStart_2426809 baseEnd_2426809 := by
    simpa [prefixWord, tailWord_2426809, baseEnd_2426809] using wordTrace_append hprefix tailTrace_2426809
  have hstable : (prefixWord ++ tailWord_2426809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426809).length < 2 ^ (prefixWord ++ tailWord_2426809).sum := by decide
  have hdescent : baseEnd_2426809 < baseStart_2426809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426824 : List Nat := [2, 1, 3, 1, 4, 1, 3, 1, 1, 5]
def baseStart_2426824 : Nat := 118140960795 + 2426824 * 2 ^ 59
def prefixEnd_2426824 : Nat := 4983230072969 + 3 ^ 40 * 2426824 * 2
def baseEnd_2426824 : Nat := 830751450577945515759497

theorem tailTrace_2426824 : CollatzResearch.WordTrace tailWord_2426824 prefixEnd_2426824 830751450577945515759497 := by
  unfold tailWord_2426824
  simp only [CollatzResearch.WordTrace]
  refine ⟨44256771480019295693391763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59009028640025727591189017 44256771480019295693391763)
  ·
    refine ⟨66385157220028943540087645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44256771480019295693391763 66385157220028943540087645)
    ·
      refine ⟨24894433957510853827532867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66385157220028943540087645 24894433957510853827532867)
      ·
        refine ⟨37341650936266280741299301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24894433957510853827532867 37341650936266280741299301)
        ·
          refine ⟨7001559550549927638993619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37341650936266280741299301 7001559550549927638993619)
          ·
            refine ⟨10502339325824891458490429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7001559550549927638993619 10502339325824891458490429)
            ·
              refine ⟨3938377247184334296933911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10502339325824891458490429 3938377247184334296933911)
              ·
                refine ⟨5907565870776501445400867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3938377247184334296933911 5907565870776501445400867)
                ·
                  refine ⟨8861348806164752168101301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5907565870776501445400867 8861348806164752168101301)
                  ·
                    refine ⟨830751450577945515759497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8861348806164752168101301 830751450577945515759497)
                    ·
                      rfl

theorem cell22_2426824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_2426824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426824 prefixEnd_2426824 := by exact prefixLift 2426824
  have htrace : WordTrace (prefixWord ++ tailWord_2426824) baseStart_2426824 baseEnd_2426824 := by
    simpa [prefixWord, tailWord_2426824, baseEnd_2426824] using wordTrace_append hprefix tailTrace_2426824
  have hstable : (prefixWord ++ tailWord_2426824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426824).length < 2 ^ (prefixWord ++ tailWord_2426824).sum := by decide
  have hdescent : baseEnd_2426824 < baseStart_2426824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426897 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 6, 5]
def baseStart_2426897 : Nat := 118140960795 + 2426897 * 2 ^ 59
def prefixEnd_2426897 : Nat := 4983230072969 + 3 ^ 40 * 2426897 * 2
def baseEnd_2426897 : Nat := 830776439969797658684273

theorem tailTrace_2426897 : CollatzResearch.WordTrace tailWord_2426897 prefixEnd_2426897 830776439969797658684273 := by
  unfold tailWord_2426897
  simp only [CollatzResearch.WordTrace]
  refine ⟨88516205488774124854190945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59010803659182749902793963 88516205488774124854190945)
  ·
    refine ⟨66387154116580593640643209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88516205488774124854190945 66387154116580593640643209)
    ·
      refine ⟨49790365587435445230482407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66387154116580593640643209 49790365587435445230482407)
      ·
        refine ⟨74685548381153167845723611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49790365587435445230482407 74685548381153167845723611)
        ·
          refine ⟨112028322571729751768585417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74685548381153167845723611 112028322571729751768585417)
          ·
            refine ⟨84021241928797313826439063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112028322571729751768585417 84021241928797313826439063)
            ·
              refine ⟨126031862893195970739658595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84021241928797313826439063 126031862893195970739658595)
              ·
                refine ⟨189047794339793956109487893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126031862893195970739658595 189047794339793956109487893)
                ·
                  refine ⟨8861615359677841692632245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 189047794339793956109487893 8861615359677841692632245)
                  ·
                    refine ⟨830776439969797658684273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8861615359677841692632245 830776439969797658684273)
                    ·
                      rfl

theorem cell22_2426897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_2426897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426897 prefixEnd_2426897 := by exact prefixLift 2426897
  have htrace : WordTrace (prefixWord ++ tailWord_2426897) baseStart_2426897 baseEnd_2426897 := by
    simpa [prefixWord, tailWord_2426897, baseEnd_2426897] using wordTrace_append hprefix tailTrace_2426897
  have hstable : (prefixWord ++ tailWord_2426897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426897).length < 2 ^ (prefixWord ++ tailWord_2426897).sum := by decide
  have hdescent : baseEnd_2426897 < baseStart_2426897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426914 : List Nat := [3, 3, 1, 1, 1, 2, 2, 2, 2, 5]
def baseStart_2426914 : Nat := 118140960795 + 2426914 * 2 ^ 59
def prefixEnd_2426914 : Nat := 4983230072969 + 3 ^ 40 * 2426914 * 2
def baseEnd_2426914 : Nat := 830782259417215281009221

theorem tailTrace_2426914 : CollatzResearch.WordTrace tailWord_2426914 prefixEnd_2426914 830782259417215281009221 := by
  unfold tailWord_2426914
  simp only [CollatzResearch.WordTrace]
  refine ⟨22129206382428134189389949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59011217019808357838373197 22129206382428134189389949)
  ·
    refine ⟨8298452393410550321021231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22129206382428134189389949 8298452393410550321021231)
    ·
      refine ⟨12447678590115825481531847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8298452393410550321021231 12447678590115825481531847)
      ·
        refine ⟨18671517885173738222297771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12447678590115825481531847 18671517885173738222297771)
        ·
          refine ⟨28007276827760607333446657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18671517885173738222297771 28007276827760607333446657)
          ·
            refine ⟨21005457620820455500084993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28007276827760607333446657 21005457620820455500084993)
            ·
              refine ⟨15754093215615341625063745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21005457620820455500084993 15754093215615341625063745)
              ·
                refine ⟨11815569911711506218797809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15754093215615341625063745 11815569911711506218797809)
                ·
                  refine ⟨8861677433783629664098357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11815569911711506218797809 8861677433783629664098357)
                  ·
                    refine ⟨830782259417215281009221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8861677433783629664098357 830782259417215281009221)
                    ·
                      rfl

theorem cell22_2426914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_2426914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426914 prefixEnd_2426914 := by exact prefixLift 2426914
  have htrace : WordTrace (prefixWord ++ tailWord_2426914) baseStart_2426914 baseEnd_2426914 := by
    simpa [prefixWord, tailWord_2426914, baseEnd_2426914] using wordTrace_append hprefix tailTrace_2426914
  have hstable : (prefixWord ++ tailWord_2426914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426914).length < 2 ^ (prefixWord ++ tailWord_2426914).sum := by decide
  have hdescent : baseEnd_2426914 < baseStart_2426914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426929 : List Nat := [1, 2, 2, 3, 1, 3, 1, 2, 3, 4]
def baseStart_2426929 : Nat := 118140960795 + 2426929 * 2 ^ 59
def prefixEnd_2426929 : Nat := 4983230072969 + 3 ^ 40 * 2426929 * 2
def baseEnd_2426929 : Nat := 830787394223760241884175

theorem tailTrace_2426929 : CollatzResearch.WordTrace tailWord_2426929 prefixEnd_2426929 830787394223760241884175 := by
  unfold tailWord_2426929
  simp only [CollatzResearch.WordTrace]
  refine ⟨88517372624658194319355841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59011581749772129546237227 88517372624658194319355841)
  ·
    refine ⟨66388029468493645739516881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88517372624658194319355841 66388029468493645739516881)
    ·
      refine ⟨49791022101370234304637661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66388029468493645739516881 49791022101370234304637661)
      ·
        refine ⟨18671633288013837864239123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49791022101370234304637661 18671633288013837864239123)
        ·
          refine ⟨28007449932020756796358685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18671633288013837864239123 28007449932020756796358685)
          ·
            refine ⟨10502793724507783798634507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28007449932020756796358685 10502793724507783798634507)
            ·
              refine ⟨15754190586761675697951761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10502793724507783798634507 15754190586761675697951761)
              ·
                refine ⟨11815642940071256773463821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15754190586761675697951761 11815642940071256773463821)
                ·
                  refine ⟨4430866102526721290048933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11815642940071256773463821 4430866102526721290048933)
                  ·
                    refine ⟨830787394223760241884175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4430866102526721290048933 830787394223760241884175)
                    ·
                      rfl

theorem cell22_2426929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_2426929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426929 prefixEnd_2426929 := by exact prefixLift 2426929
  have htrace : WordTrace (prefixWord ++ tailWord_2426929) baseStart_2426929 baseEnd_2426929 := by
    simpa [prefixWord, tailWord_2426929, baseEnd_2426929] using wordTrace_append hprefix tailTrace_2426929
  have hstable : (prefixWord ++ tailWord_2426929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426929).length < 2 ^ (prefixWord ++ tailWord_2426929).sum := by decide
  have hdescent : baseEnd_2426929 < baseStart_2426929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426944 : List Nat := [2, 1, 1, 2, 2, 5, 1, 2, 6]
def baseStart_2426944 : Nat := 118140960795 + 2426944 * 2 ^ 59
def prefixEnd_2426944 : Nat := 4983230072969 + 3 ^ 40 * 2426944 * 2
def baseEnd_2426944 : Nat := 276930843010101734253043

theorem tailTrace_2426944 : CollatzResearch.WordTrace tailWord_2426944 prefixEnd_2426944 276930843010101734253043 := by
  unfold tailWord_2426944
  simp only [CollatzResearch.WordTrace]
  refine ⟨44258959859801925940575943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59011946479735901254101257 44258959859801925940575943)
  ·
    refine ⟨66388439789702888910863915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44258959859801925940575943 66388439789702888910863915)
    ·
      refine ⟨99582659684554333366295873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66388439789702888910863915 99582659684554333366295873)
      ·
        refine ⟨74686994763415750024721905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99582659684554333366295873 74686994763415750024721905)
        ·
          refine ⟨56015246072561812518541429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74686994763415750024721905 56015246072561812518541429)
          ·
            refine ⟨5251429319302669923613259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56015246072561812518541429 5251429319302669923613259)
            ·
              refine ⟨7877143978954004885419889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5251429319302669923613259 7877143978954004885419889)
              ·
                refine ⟨5907857984215503664064917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7877143978954004885419889 5907857984215503664064917)
                ·
                  refine ⟨276930843010101734253043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5907857984215503664064917 276930843010101734253043)
                  ·
                    rfl

theorem cell22_2426944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 6].length) (baseStart_2426944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426944 prefixEnd_2426944 := by exact prefixLift 2426944
  have htrace : WordTrace (prefixWord ++ tailWord_2426944) baseStart_2426944 baseEnd_2426944 := by
    simpa [prefixWord, tailWord_2426944, baseEnd_2426944] using wordTrace_append hprefix tailTrace_2426944
  have hstable : (prefixWord ++ tailWord_2426944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426944).length < 2 ^ (prefixWord ++ tailWord_2426944).sum := by decide
  have hdescent : baseEnd_2426944 < baseStart_2426944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426959 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 6, 3]
def baseStart_2426959 : Nat := 118140960795 + 2426959 * 2 ^ 59
def prefixEnd_2426959 : Nat := 4983230072969 + 3 ^ 40 * 2426959 * 2
def baseEnd_2426959 : Nat := 830797663836850163634083

theorem tailTrace_2426959 : CollatzResearch.WordTrace tailWord_2426959 prefixEnd_2426959 830797663836850163634083 := by
  unfold tailWord_2426959
  simp only [CollatzResearch.WordTrace]
  refine ⟨88518466814549509442947931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59012311209699672961965287 88518466814549509442947931)
  ·
    refine ⟨132777700221824264164421897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88518466814549509442947931 132777700221824264164421897)
    ·
      refine ⟨99583275166368198123316423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132777700221824264164421897 99583275166368198123316423)
      ·
        refine ⟨149374912749552297184974635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99583275166368198123316423 149374912749552297184974635)
        ·
          refine ⟨224062369124328445777461953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149374912749552297184974635 224062369124328445777461953)
          ·
            refine ⟨168046776843246334333096465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224062369124328445777461953 168046776843246334333096465)
            ·
              refine ⟨126035082632434750749822349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168046776843246334333096465 126035082632434750749822349)
              ·
                refine ⟨47263155987163031531183381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126035082632434750749822349 47263155987163031531183381)
                ·
                  refine ⟨2215460436898267103024221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47263155987163031531183381 2215460436898267103024221)
                  ·
                    refine ⟨830797663836850163634083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2215460436898267103024221 830797663836850163634083)
                    ·
                      rfl

theorem cell22_2426959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 6, 3].length) (baseStart_2426959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426959 prefixEnd_2426959 := by exact prefixLift 2426959
  have htrace : WordTrace (prefixWord ++ tailWord_2426959) baseStart_2426959 baseEnd_2426959 := by
    simpa [prefixWord, tailWord_2426959, baseEnd_2426959] using wordTrace_append hprefix tailTrace_2426959
  have hstable : (prefixWord ++ tailWord_2426959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426959).length < 2 ^ (prefixWord ++ tailWord_2426959).sum := by decide
  have hdescent : baseEnd_2426959 < baseStart_2426959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426976 : List Nat := [2, 1, 1, 3, 2, 4, 1, 1, 4, 3]
def baseStart_2426976 : Nat := 118140960795 + 2426976 * 2 ^ 59
def prefixEnd_2426976 : Nat := 4983230072969 + 3 ^ 40 * 2426976 * 2
def baseEnd_2426976 : Nat := 830803483284267785959031

theorem tailTrace_2426976 : CollatzResearch.WordTrace tailWord_2426976 prefixEnd_2426976 830803483284267785959031 := by
  unfold tailWord_2426976
  simp only [CollatzResearch.WordTrace]
  refine ⟨44259543427743960673158391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59012724570325280897544521 44259543427743960673158391)
  ·
    refine ⟨66389315141615941009737587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44259543427743960673158391 66389315141615941009737587)
    ·
      refine ⟨99583972712423911514606381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66389315141615941009737587 99583972712423911514606381)
      ·
        refine ⟨37343989767158966817977393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99583972712423911514606381 37343989767158966817977393)
        ·
          refine ⟨28007992325369225113483045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37343989767158966817977393 28007992325369225113483045)
          ·
            refine ⟨5251498561006729708778071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28007992325369225113483045 5251498561006729708778071)
            ·
              refine ⟨7877247841510094563167107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5251498561006729708778071 7877247841510094563167107)
              ·
                refine ⟨11815871762265141844750661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7877247841510094563167107 11815871762265141844750661)
                ·
                  refine ⟨2215475955424714095890749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11815871762265141844750661 2215475955424714095890749)
                  ·
                    refine ⟨830803483284267785959031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2215475955424714095890749 830803483284267785959031)
                    ·
                      rfl

theorem cell22_2426976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 4, 3].length) (baseStart_2426976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426976 prefixEnd_2426976 := by exact prefixLift 2426976
  have htrace : WordTrace (prefixWord ++ tailWord_2426976) baseStart_2426976 baseEnd_2426976 := by
    simpa [prefixWord, tailWord_2426976, baseEnd_2426976] using wordTrace_append hprefix tailTrace_2426976
  have hstable : (prefixWord ++ tailWord_2426976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426976).length < 2 ^ (prefixWord ++ tailWord_2426976).sum := by decide
  have hdescent : baseEnd_2426976 < baseStart_2426976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426978 : List Nat := [3, 3, 2, 2, 2, 1, 2, 1, 6]
def baseStart_2426978 : Nat := 118140960795 + 2426978 * 2 ^ 59
def prefixEnd_2426978 : Nat := 4983230072969 + 3 ^ 40 * 2426978 * 2
def baseEnd_2426978 : Nat := 276934722641713482469675

theorem tailTrace_2426978 : CollatzResearch.WordTrace tailWord_2426978 prefixEnd_2426978 276934722641713482469675 := by
  unfold tailWord_2426978
  simp only [CollatzResearch.WordTrace]
  refine ⟨22129789950370168921972397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59012773200987117125259725 22129789950370168921972397)
  ·
    refine ⟨8298671231388813345739649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22129789950370168921972397 8298671231388813345739649)
    ·
      refine ⟨6224003423541610009304737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8298671231388813345739649 6224003423541610009304737)
      ·
        refine ⟨4668002567656207506978553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6224003423541610009304737 4668002567656207506978553)
        ·
          refine ⟨3501001925742155630233915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4668002567656207506978553 3501001925742155630233915)
          ·
            refine ⟨5251502888613233445350873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3501001925742155630233915 5251502888613233445350873)
            ·
              refine ⟨3938627166459925084013155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5251502888613233445350873 3938627166459925084013155)
              ·
                refine ⟨5907940749689887626019733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3938627166459925084013155 5907940749689887626019733)
                ·
                  refine ⟨276934722641713482469675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5907940749689887626019733 276934722641713482469675)
                  ·
                    rfl

theorem cell22_2426978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_2426978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426978 prefixEnd_2426978 := by exact prefixLift 2426978
  have htrace : WordTrace (prefixWord ++ tailWord_2426978) baseStart_2426978 baseEnd_2426978 := by
    simpa [prefixWord, tailWord_2426978, baseEnd_2426978] using wordTrace_append hprefix tailTrace_2426978
  have hstable : (prefixWord ++ tailWord_2426978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426978).length < 2 ^ (prefixWord ++ tailWord_2426978).sum := by decide
  have hdescent : baseEnd_2426978 < baseStart_2426978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426989 : List Nat := [1, 5, 1, 1, 2, 1, 2, 9]
def baseStart_2426989 : Nat := 118140960795 + 2426989 * 2 ^ 59
def prefixEnd_2426989 : Nat := 4983230072969 + 3 ^ 40 * 2426989 * 2
def baseEnd_2426989 : Nat := 92311992605548898375999

theorem tailTrace_2426989 : CollatzResearch.WordTrace tailWord_2426989 prefixEnd_2426989 92311992605548898375999 := by
  unfold tailWord_2426989
  simp only [CollatzResearch.WordTrace]
  refine ⟨88519561004440824566540021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59013040669627216377693347 88519561004440824566540021)
  ·
    refine ⟨8298708844166327303113127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88519561004440824566540021 8298708844166327303113127)
    ·
      refine ⟨12448063266249490954669691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8298708844166327303113127 12448063266249490954669691)
      ·
        refine ⟨18672094899374236432004537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12448063266249490954669691 18672094899374236432004537)
        ·
          refine ⟨14004071174530677324003403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18672094899374236432004537 14004071174530677324003403)
          ·
            refine ⟨21006106761796015986005105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14004071174530677324003403 21006106761796015986005105)
            ·
              refine ⟨15754580071347011989503829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21006106761796015986005105 15754580071347011989503829)
              ·
                refine ⟨92311992605548898375999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15754580071347011989503829 92311992605548898375999)
                ·
                  rfl

theorem cell22_2426989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 9].length) (baseStart_2426989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426989 prefixEnd_2426989 := by exact prefixLift 2426989
  have htrace : WordTrace (prefixWord ++ tailWord_2426989) baseStart_2426989 baseEnd_2426989 := by
    simpa [prefixWord, tailWord_2426989, baseEnd_2426989] using wordTrace_append hprefix tailTrace_2426989
  have hstable : (prefixWord ++ tailWord_2426989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426989).length < 2 ^ (prefixWord ++ tailWord_2426989).sum := by decide
  have hdescent : baseEnd_2426989 < baseStart_2426989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426993 : List Nat := [1, 2, 2, 2, 1, 1, 7, 1, 2, 3]
def baseStart_2426993 : Nat := 118140960795 + 2426993 * 2 ^ 59
def prefixEnd_2426993 : Nat := 4983230072969 + 3 ^ 40 * 2426993 * 2
def baseEnd_2426993 : Nat := 830809302731685408283979

theorem tailTrace_2426993 : CollatzResearch.WordTrace tailWord_2426993 prefixEnd_2426993 830809302731685408283979 := by
  unfold tailWord_2426993
  simp only [CollatzResearch.WordTrace]
  refine ⟨88519706896426333249685633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59013137930950888833123755 88519706896426333249685633)
  ·
    refine ⟨66389780172319749937264225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88519706896426333249685633 66389780172319749937264225)
    ·
      refine ⟨49792335129239812452948169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66389780172319749937264225 49792335129239812452948169)
      ·
        refine ⟨37344251346929859339711127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49792335129239812452948169 37344251346929859339711127)
        ·
          refine ⟨56016377020394789009566691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37344251346929859339711127 56016377020394789009566691)
          ·
            refine ⟨84024565530592183514350037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56016377020394789009566691 84024565530592183514350037)
            ·
              refine ⟨1969325754623254301117579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 84024565530592183514350037 1969325754623254301117579)
              ·
                refine ⟨2953988631934881451676369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1969325754623254301117579 2953988631934881451676369)
                ·
                  refine ⟨2215491473951161088757277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2953988631934881451676369 2215491473951161088757277)
                  ·
                    refine ⟨830809302731685408283979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2215491473951161088757277 830809302731685408283979)
                    ·
                      rfl

theorem cell22_2426993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 2, 3].length) (baseStart_2426993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2426993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2426993 prefixEnd_2426993 := by exact prefixLift 2426993
  have htrace : WordTrace (prefixWord ++ tailWord_2426993) baseStart_2426993 baseEnd_2426993 := by
    simpa [prefixWord, tailWord_2426993, baseEnd_2426993] using wordTrace_append hprefix tailTrace_2426993
  have hstable : (prefixWord ++ tailWord_2426993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426993).length < 2 ^ (prefixWord ++ tailWord_2426993).sum := by decide
  have hdescent : baseEnd_2426993 < baseStart_2426993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427100 : List Nat := [2, 2, 5, 2, 1, 1, 1, 1, 2, 5]
def baseStart_2427100 : Nat := 118140960795 + 2427100 * 2 ^ 59
def prefixEnd_2427100 : Nat := 4983230072969 + 3 ^ 40 * 2427100 * 2
def baseEnd_2427100 : Nat := 830845931018372795858651

theorem tailTrace_2427100 : CollatzResearch.WordTrace tailWord_2427100 prefixEnd_2427100 830845931018372795858651 := by
  unfold tailWord_2427100
  simp only [CollatzResearch.WordTrace]
  refine ⟨44261804753519345261915377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59015739671359127015887169 44261804753519345261915377)
  ·
    refine ⟨33196353565139508946436533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44261804753519345261915377 33196353565139508946436533)
    ·
      refine ⟨3112158146731828963728425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33196353565139508946436533 3112158146731828963728425)
      ·
        refine ⟨2334118610048871722796319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3112158146731828963728425 2334118610048871722796319)
        ·
          refine ⟨3501177915073307584194479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2334118610048871722796319 3501177915073307584194479)
          ·
            refine ⟨5251766872609961376291719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3501177915073307584194479 5251766872609961376291719)
            ·
              refine ⟨7877650308914942064437579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5251766872609961376291719 7877650308914942064437579)
              ·
                refine ⟨11816475463372413096656369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7877650308914942064437579 11816475463372413096656369)
                ·
                  refine ⟨8862356597529309822492277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11816475463372413096656369 8862356597529309822492277)
                  ·
                    refine ⟨830845931018372795858651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8862356597529309822492277 830845931018372795858651)
                    ·
                      rfl

theorem cell22_2427100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_2427100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2427100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2427100 prefixEnd_2427100 := by exact prefixLift 2427100
  have htrace : WordTrace (prefixWord ++ tailWord_2427100) baseStart_2427100 baseEnd_2427100 := by
    simpa [prefixWord, tailWord_2427100, baseEnd_2427100] using wordTrace_append hprefix tailTrace_2427100
  have hstable : (prefixWord ++ tailWord_2427100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427100).length < 2 ^ (prefixWord ++ tailWord_2427100).sum := by decide
  have hdescent : baseEnd_2427100 < baseStart_2427100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427145 : List Nat := [1, 2, 1, 1, 3, 6, 1, 2, 2, 3]
def baseStart_2427145 : Nat := 118140960795 + 2427145 * 2 ^ 59
def prefixEnd_2427145 : Nat := 4983230072969 + 3 ^ 40 * 2427145 * 2
def baseEnd_2427145 : Nat := 830861335438007678483513

theorem tailTrace_2427145 : CollatzResearch.WordTrace tailWord_2427145 prefixEnd_2427145 830861335438007678483513 := by
  unfold tailWord_2427145
  simp only [CollatzResearch.WordTrace]
  refine ⟨88525250791875663209218889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59016833861250442139479259 88525250791875663209218889)
  ·
    refine ⟨66393938093906747406914167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88525250791875663209218889 66393938093906747406914167)
    ·
      refine ⟨99590907140860121110371251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66393938093906747406914167 99590907140860121110371251)
      ·
        refine ⟨149386360711290181665556877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99590907140860121110371251 149386360711290181665556877)
        ·
          refine ⟨56019885266733818124583829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149386360711290181665556877 56019885266733818124583829)
          ·
            refine ⟨2625932121878147724589867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 56019885266733818124583829 2625932121878147724589867)
            ·
              refine ⟨3938898182817221586884801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2625932121878147724589867 3938898182817221586884801)
              ·
                refine ⟨2954173637112916190163601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3938898182817221586884801 2954173637112916190163601)
                ·
                  refine ⟨2215630227834687142622701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2954173637112916190163601 2215630227834687142622701)
                  ·
                    refine ⟨830861335438007678483513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2215630227834687142622701 830861335438007678483513)
                    ·
                      rfl

theorem cell22_2427145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 2, 3].length) (baseStart_2427145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2427145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2427145 prefixEnd_2427145 := by exact prefixLift 2427145
  have htrace : WordTrace (prefixWord ++ tailWord_2427145) baseStart_2427145 baseEnd_2427145 := by
    simpa [prefixWord, tailWord_2427145, baseEnd_2427145] using wordTrace_append hprefix tailTrace_2427145
  have hstable : (prefixWord ++ tailWord_2427145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427145).length < 2 ^ (prefixWord ++ tailWord_2427145).sum := by decide
  have hdescent : baseEnd_2427145 < baseStart_2427145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427162 : List Nat := [3, 1, 1, 3, 4, 1, 3, 1, 2, 3]
def baseStart_2427162 : Nat := 118140960795 + 2427162 * 2 ^ 59
def prefixEnd_2427162 : Nat := 4983230072969 + 3 ^ 40 * 2427162 * 2
def baseEnd_2427162 : Nat := 830867154885425300808461

theorem tailTrace_2427162 : CollatzResearch.WordTrace tailWord_2427162 prefixEnd_2427162 830867154885425300808461 := by
  unfold tailWord_2427162
  simp only [CollatzResearch.WordTrace]
  refine ⟨22131467708203518778146935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59017247221876050075058493 22131467708203518778146935)
  ·
    refine ⟨33197201562305278167220403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22131467708203518778146935 33197201562305278167220403)
    ·
      refine ⟨49795802343457917250830605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33197201562305278167220403 49795802343457917250830605)
      ·
        refine ⟨18673425878796718969061477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49795802343457917250830605 18673425878796718969061477)
        ·
          refine ⟨3501267352274384806699027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18673425878796718969061477 3501267352274384806699027)
          ·
            refine ⟨5251901028411577210048541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3501267352274384806699027 5251901028411577210048541)
            ·
              refine ⟨1969462885654341453768203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5251901028411577210048541 1969462885654341453768203)
              ·
                refine ⟨2954194328481512180652305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1969462885654341453768203 2954194328481512180652305)
                ·
                  refine ⟨2215645746361134135489229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2954194328481512180652305 2215645746361134135489229)
                  ·
                    refine ⟨830867154885425300808461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2215645746361134135489229 830867154885425300808461)
                    ·
                      rfl

theorem cell22_2427162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 2, 3].length) (baseStart_2427162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2427162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2427162 prefixEnd_2427162 := by exact prefixLift 2427162
  have htrace : WordTrace (prefixWord ++ tailWord_2427162) baseStart_2427162 baseEnd_2427162 := by
    simpa [prefixWord, tailWord_2427162, baseEnd_2427162] using wordTrace_append hprefix tailTrace_2427162
  have hstable : (prefixWord ++ tailWord_2427162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427162).length < 2 ^ (prefixWord ++ tailWord_2427162).sum := by decide
  have hdescent : baseEnd_2427162 < baseStart_2427162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427207 : List Nat := [1, 1, 4, 1, 2, 2, 5, 2, 1, 3]
def baseStart_2427207 : Nat := 118140960795 + 2427207 * 2 ^ 59
def prefixEnd_2427207 : Nat := 4983230072969 + 3 ^ 40 * 2427207 * 2
def baseEnd_2427207 : Nat := 830882559305060183433323

theorem tailTrace_2427207 : CollatzResearch.WordTrace tailWord_2427207 prefixEnd_2427207 830882559305060183433323 := by
  unfold tailWord_2427207
  simp only [CollatzResearch.WordTrace]
  refine ⟨88527512117651047797975875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59018341411767365198650583 88527512117651047797975875)
  ·
    refine ⟨132791268176476571696963813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88527512117651047797975875 132791268176476571696963813)
    ·
      refine ⟨24898362783089357193180715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132791268176476571696963813 24898362783089357193180715)
      ·
        refine ⟨37347544174634035789771073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24898362783089357193180715 37347544174634035789771073)
        ·
          refine ⟨28010658130975526842328305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37347544174634035789771073 28010658130975526842328305)
          ·
            refine ⟨21007993598231645131746229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28010658130975526842328305 21007993598231645131746229)
            ·
              refine ⟨1969499399834216731101209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21007993598231645131746229 1969499399834216731101209)
              ·
                refine ⟨1477124549875662548325907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1969499399834216731101209 1477124549875662548325907)
                ·
                  refine ⟨2215686824813493822488861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1477124549875662548325907 2215686824813493822488861)
                  ·
                    refine ⟨830882559305060183433323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2215686824813493822488861 830882559305060183433323)
                    ·
                      rfl

theorem cell22_2427207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_2427207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2427207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2427207 prefixEnd_2427207 := by exact prefixLift 2427207
  have htrace : WordTrace (prefixWord ++ tailWord_2427207) baseStart_2427207 baseEnd_2427207 := by
    simpa [prefixWord, tailWord_2427207, baseEnd_2427207] using wordTrace_append hprefix tailTrace_2427207
  have hstable : (prefixWord ++ tailWord_2427207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427207).length < 2 ^ (prefixWord ++ tailWord_2427207).sum := by decide
  have hdescent : baseEnd_2427207 < baseStart_2427207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427220 : List Nat := [2, 4, 1, 1, 2, 2, 4, 1, 5]
def baseStart_2427220 : Nat := 118140960795 + 2427220 * 2 ^ 59
def prefixEnd_2427220 : Nat := 4983230072969 + 3 ^ 40 * 2427220 * 2
def baseEnd_2427220 : Nat := 276962336490244160952761

theorem tailTrace_2427220 : CollatzResearch.WordTrace tailWord_2427220 prefixEnd_2427220 276962336490244160952761 := by
  unfold tailWord_2427220
  simp only [CollatzResearch.WordTrace]
  refine ⟨44263993133301975509099557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59018657511069300678799409 44263993133301975509099557)
  ·
    refine ⟨8299498712494120407956167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44263993133301975509099557 8299498712494120407956167)
    ·
      refine ⟨12449248068741180611934251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8299498712494120407956167 12449248068741180611934251)
      ·
        refine ⟨18673872103111770917901377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12449248068741180611934251 18673872103111770917901377)
        ·
          refine ⟨14005404077333828188426033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18673872103111770917901377 14005404077333828188426033)
          ·
            refine ⟨10504053058000371141319525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14005404077333828188426033 10504053058000371141319525)
            ·
              refine ⟨1969509948375069588997411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10504053058000371141319525 1969509948375069588997411)
              ·
                refine ⟨2954264922562604383496117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1969509948375069588997411 2954264922562604383496117)
                ·
                  refine ⟨276962336490244160952761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2954264922562604383496117 276962336490244160952761)
                  ·
                    rfl

theorem cell22_2427220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_2427220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2427220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2427220 prefixEnd_2427220 := by exact prefixLift 2427220
  have htrace : WordTrace (prefixWord ++ tailWord_2427220) baseStart_2427220 baseEnd_2427220 := by
    simpa [prefixWord, tailWord_2427220, baseEnd_2427220] using wordTrace_append hprefix tailTrace_2427220
  have hstable : (prefixWord ++ tailWord_2427220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427220).length < 2 ^ (prefixWord ++ tailWord_2427220).sum := by decide
  have hdescent : baseEnd_2427220 < baseStart_2427220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427231 : List Nat := [1, 1, 2, 3, 1, 2, 2, 4, 6]
def baseStart_2427231 : Nat := 118140960795 + 2427231 * 2 ^ 59
def prefixEnd_2427231 : Nat := 4983230072969 + 3 ^ 40 * 2427231 * 2
def baseEnd_2427231 : Nat := 276963591665177373611083

theorem tailTrace_2427231 : CollatzResearch.WordTrace tailWord_2427231 prefixEnd_2427231 276963591665177373611083 := by
  unfold tailWord_2427231
  simp only [CollatzResearch.WordTrace]
  refine ⟨88528387469564099896849547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59018924979709399931233031 88528387469564099896849547)
  ·
    refine ⟨132792581204346149845274321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88528387469564099896849547 132792581204346149845274321)
    ·
      refine ⟨99594435903259612383955741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132792581204346149845274321 99594435903259612383955741)
      ·
        refine ⟨37347913463722354643983403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99594435903259612383955741 37347913463722354643983403)
        ·
          refine ⟨56021870195583531965975105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37347913463722354643983403 56021870195583531965975105)
          ·
            refine ⟨42016402646687648974481329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56021870195583531965975105 42016402646687648974481329)
            ·
              refine ⟨31512301985015736730860997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42016402646687648974481329 31512301985015736730860997)
              ·
                refine ⟨5908556622190450637036437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31512301985015736730860997 5908556622190450637036437)
                ·
                  refine ⟨276963591665177373611083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5908556622190450637036437 276963591665177373611083)
                  ·
                    rfl

theorem cell22_2427231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 6].length) (baseStart_2427231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2427231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2427231 prefixEnd_2427231 := by exact prefixLift 2427231
  have htrace : WordTrace (prefixWord ++ tailWord_2427231) baseStart_2427231 baseEnd_2427231 := by
    simpa [prefixWord, tailWord_2427231, baseEnd_2427231] using wordTrace_append hprefix tailTrace_2427231
  have hstable : (prefixWord ++ tailWord_2427231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427231).length < 2 ^ (prefixWord ++ tailWord_2427231).sum := by decide
  have hdescent : baseEnd_2427231 < baseStart_2427231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427308 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 7, 3]
def baseStart_2427308 : Nat := 118140960795 + 2427308 * 2 ^ 59
def prefixEnd_2427308 : Nat := 4983230072969 + 3 ^ 40 * 2427308 * 2
def baseEnd_2427308 : Nat := 830917133669129586658013

theorem tailTrace_2427308 : CollatzResearch.WordTrace tailWord_2427308 prefixEnd_2427308 830917133669129586658013 := by
  unfold tailWord_2427308
  simp only [CollatzResearch.WordTrace]
  refine ⟨44265597945142571023701289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59020797260190094698268385 44265597945142571023701289)
  ·
    refine ⟨33199198458856928267775967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44265597945142571023701289 33199198458856928267775967)
    ·
      refine ⟨49798797688285392401663951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33199198458856928267775967 49798797688285392401663951)
      ·
        refine ⟨74698196532428088602495927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49798797688285392401663951 74698196532428088602495927)
        ·
          refine ⟨112047294798642132903743891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74698196532428088602495927 112047294798642132903743891)
          ·
            refine ⟨168070942197963199355615837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112047294798642132903743891 168070942197963199355615837)
            ·
              refine ⟨63026603324236199758355939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168070942197963199355615837 63026603324236199758355939)
              ·
                refine ⟨94539904986354299637533909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63026603324236199758355939 94539904986354299637533909)
                ·
                  refine ⟨2215779023117678897754701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 94539904986354299637533909 2215779023117678897754701)
                  ·
                    refine ⟨830917133669129586658013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2215779023117678897754701 830917133669129586658013)
                    ·
                      rfl

theorem cell22_2427308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 3].length) (baseStart_2427308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2427308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2427308 prefixEnd_2427308 := by exact prefixLift 2427308
  have htrace : WordTrace (prefixWord ++ tailWord_2427308) baseStart_2427308 baseEnd_2427308 := by
    simpa [prefixWord, tailWord_2427308, baseEnd_2427308] using wordTrace_append hprefix tailTrace_2427308
  have hstable : (prefixWord ++ tailWord_2427308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427308).length < 2 ^ (prefixWord ++ tailWord_2427308).sum := by decide
  have hdescent : baseEnd_2427308 < baseStart_2427308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427325 : List Nat := [1, 4, 1, 2, 2, 2, 1, 3, 3, 3]
def baseStart_2427325 : Nat := 118140960795 + 2427325 * 2 ^ 59
def prefixEnd_2427325 : Nat := 4983230072969 + 3 ^ 40 * 2427325 * 2
def baseEnd_2427325 : Nat := 830922953116547208982961

theorem tailTrace_2427325 : CollatzResearch.WordTrace tailWord_2427325 prefixEnd_2427325 830922953116547208982961 := by
  unfold tailWord_2427325
  simp only [CollatzResearch.WordTrace]
  refine ⟨88531815931223553950771429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59021210620815702633847619 88531815931223553950771429)
  ·
    refine ⟨16599715487104416365769643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88531815931223553950771429 16599715487104416365769643)
    ·
      refine ⟨24899573230656624548654465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16599715487104416365769643 24899573230656624548654465)
      ·
        refine ⟨18674679922992468411490849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24899573230656624548654465 18674679922992468411490849)
        ·
          refine ⟨14006009942244351308618137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18674679922992468411490849 14006009942244351308618137)
          ·
            refine ⟨10504507456683263481463603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14006009942244351308618137 10504507456683263481463603)
            ·
              refine ⟨15756761185024895222195405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10504507456683263481463603 15756761185024895222195405)
              ·
                refine ⟨5908785444384335708323277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15756761185024895222195405 5908785444384335708323277)
                ·
                  refine ⟨2215794541644125890621229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5908785444384335708323277 2215794541644125890621229)
                  ·
                    refine ⟨830922953116547208982961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2215794541644125890621229 830922953116547208982961)
                    ·
                      rfl

theorem cell22_2427325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_2427325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2427325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2427325 prefixEnd_2427325 := by exact prefixLift 2427325
  have htrace : WordTrace (prefixWord ++ tailWord_2427325) baseStart_2427325 baseEnd_2427325 := by
    simpa [prefixWord, tailWord_2427325, baseEnd_2427325] using wordTrace_append hprefix tailTrace_2427325
  have hstable : (prefixWord ++ tailWord_2427325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427325).length < 2 ^ (prefixWord ++ tailWord_2427325).sum := by decide
  have hdescent : baseEnd_2427325 < baseStart_2427325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427359 : List Nat := [1, 1, 2, 3, 3, 4, 1, 3, 1, 3]
def baseStart_2427359 : Nat := 118140960795 + 2427359 * 2 ^ 59
def prefixEnd_2427359 : Nat := 4983230072969 + 3 ^ 40 * 2427359 * 2
def baseEnd_2427359 : Nat := 830934592011382453632857

theorem tailTrace_2427359 : CollatzResearch.WordTrace tailWord_2427359 prefixEnd_2427359 830934592011382453632857 := by
  unfold tailWord_2427359
  simp only [CollatzResearch.WordTrace]
  refine ⟨88533056013100377757509131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59022037342066918505006087 88533056013100377757509131)
  ·
    refine ⟨132799584019650566636263697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88533056013100377757509131 132799584019650566636263697)
    ·
      refine ⟨99599688014737924977197773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132799584019650566636263697 99599688014737924977197773)
      ·
        refine ⟨37349883005526721866449165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99599688014737924977197773 37349883005526721866449165)
        ·
          refine ⟨14006206127072520699918437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37349883005526721866449165 14006206127072520699918437)
          ·
            refine ⟨2626163648826097631234707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14006206127072520699918437 2626163648826097631234707)
            ·
              refine ⟨3939245473239146446852061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2626163648826097631234707 3939245473239146446852061)
              ·
                refine ⟨1477217052464679917569523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3939245473239146446852061 1477217052464679917569523)
                ·
                  refine ⟨2215825578697019876354285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1477217052464679917569523 2215825578697019876354285)
                  ·
                    refine ⟨830934592011382453632857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2215825578697019876354285 830934592011382453632857)
                    ·
                      rfl

theorem cell22_2427359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 3, 1, 3].length) (baseStart_2427359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2427359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2427359 prefixEnd_2427359 := by exact prefixLift 2427359
  have htrace : WordTrace (prefixWord ++ tailWord_2427359) baseStart_2427359 baseEnd_2427359 := by
    simpa [prefixWord, tailWord_2427359, baseEnd_2427359] using wordTrace_append hprefix tailTrace_2427359
  have hstable : (prefixWord ++ tailWord_2427359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427359).length < 2 ^ (prefixWord ++ tailWord_2427359).sum := by decide
  have hdescent : baseEnd_2427359 < baseStart_2427359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427434 : List Nat := [3, 1, 4, 1, 1, 2, 4, 2, 4]
def baseStart_2427434 : Nat := 118140960795 + 2427434 * 2 ^ 59
def prefixEnd_2427434 : Nat := 4983230072969 + 3 ^ 40 * 2427434 * 2
def baseEnd_2427434 : Nat := 276986755348035752669209

theorem tailTrace_2427434 : CollatzResearch.WordTrace tailWord_2427434 prefixEnd_2427434 276986755348035752669209 := by
  unfold tailWord_2427434
  simp only [CollatzResearch.WordTrace]
  refine ⟨22133947871957166391622339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59023860991885777044326237 22133947871957166391622339)
  ·
    refine ⟨33200921807935749587433509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22133947871957166391622339 33200921807935749587433509)
    ·
      refine ⟨6225172838987953047643783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33200921807935749587433509 6225172838987953047643783)
      ·
        refine ⟨9337759258481929571465675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6225172838987953047643783 9337759258481929571465675)
        ·
          refine ⟨14006638887722894357198513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9337759258481929571465675 14006638887722894357198513)
          ·
            refine ⟨10504979165792170767898885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14006638887722894357198513 10504979165792170767898885)
            ·
              refine ⟨1969683593586032018981041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10504979165792170767898885 1969683593586032018981041)
              ·
                refine ⟨1477262695189524014235781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1969683593586032018981041 1477262695189524014235781)
                ·
                  refine ⟨276986755348035752669209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1477262695189524014235781 276986755348035752669209)
                  ·
                    rfl

theorem cell22_2427434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 2, 4].length) (baseStart_2427434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2427434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2427434 prefixEnd_2427434 := by exact prefixLift 2427434
  have htrace : WordTrace (prefixWord ++ tailWord_2427434) baseStart_2427434 baseEnd_2427434 := by
    simpa [prefixWord, tailWord_2427434, baseEnd_2427434] using wordTrace_append hprefix tailTrace_2427434
  have hstable : (prefixWord ++ tailWord_2427434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427434).length < 2 ^ (prefixWord ++ tailWord_2427434).sum := by decide
  have hdescent : baseEnd_2427434 < baseStart_2427434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427580 : List Nat := [2, 2, 2, 3, 1, 1, 1, 10]
def baseStart_2427580 : Nat := 118140960795 + 2427580 * 2 ^ 59
def prefixEnd_2427580 : Nat := 4983230072969 + 3 ^ 40 * 2427580 * 2
def baseEnd_2427580 : Nat := 92334471647534615984131

theorem tailTrace_2427580 : CollatzResearch.WordTrace tailWord_2427580 prefixEnd_2427580 92334471647534615984131 := by
  unfold tailWord_2427580
  simp only [CollatzResearch.WordTrace]
  refine ⟨44270558272649866250652097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59027411030199821667536129 44270558272649866250652097)
  ·
    refine ⟨33202918704487399687989073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44270558272649866250652097 33202918704487399687989073)
    ·
      refine ⟨24902189028365549765991805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33202918704487399687989073 24902189028365549765991805)
      ·
        refine ⟨9338320885637081162246927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24902189028365549765991805 9338320885637081162246927)
        ·
          refine ⟨14007481328455621743370391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9338320885637081162246927 14007481328455621743370391)
          ·
            refine ⟨21011221992683432615055587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14007481328455621743370391 21011221992683432615055587)
            ·
              refine ⟨31516832989025148922583381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21011221992683432615055587 31516832989025148922583381)
              ·
                refine ⟨92334471647534615984131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31516832989025148922583381 92334471647534615984131)
                ·
                  rfl

theorem cell22_2427580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 10].length) (baseStart_2427580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2427580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2427580 prefixEnd_2427580 := by exact prefixLift 2427580
  have htrace : WordTrace (prefixWord ++ tailWord_2427580) baseStart_2427580 baseEnd_2427580 := by
    simpa [prefixWord, tailWord_2427580, baseEnd_2427580] using wordTrace_append hprefix tailTrace_2427580
  have hstable : (prefixWord ++ tailWord_2427580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427580).length < 2 ^ (prefixWord ++ tailWord_2427580).sum := by decide
  have hdescent : baseEnd_2427580 < baseStart_2427580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427597 : List Nat := [1, 6, 2, 1, 12]
def baseStart_2427597 : Nat := 118140960795 + 2427597 * 2 ^ 59
def prefixEnd_2427597 : Nat := 4983230072969 + 3 ^ 40 * 2427597 * 2
def baseEnd_2427597 : Nat := 3419819194548268173589

theorem tailTrace_2427597 : CollatzResearch.WordTrace tailWord_2427597 prefixEnd_2427597 3419819194548268173589 := by
  unfold tailWord_2427597
  simp only [CollatzResearch.WordTrace]
  refine ⟨88541736586238144404673045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59027824390825429603115363 88541736586238144404673045)
  ·
    refine ⟨4150393902479913018969049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 88541736586238144404673045 4150393902479913018969049)
    ·
      refine ⟨3112795426859934764226787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4150393902479913018969049 3112795426859934764226787)
      ·
        refine ⟨4669193140289902146340181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3112795426859934764226787 4669193140289902146340181)
        ·
          refine ⟨3419819194548268173589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4669193140289902146340181 3419819194548268173589)
          ·
            rfl

theorem cell22_2427597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 12].length) (baseStart_2427597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2427597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2427597 prefixEnd_2427597 := by exact prefixLift 2427597
  have htrace : WordTrace (prefixWord ++ tailWord_2427597) baseStart_2427597 baseEnd_2427597 := by
    simpa [prefixWord, tailWord_2427597, baseEnd_2427597] using wordTrace_append hprefix tailTrace_2427597
  have hstable : (prefixWord ++ tailWord_2427597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427597).length < 2 ^ (prefixWord ++ tailWord_2427597).sum := by decide
  have hdescent : baseEnd_2427597 < baseStart_2427597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427610 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 1, 8]
def baseStart_2427610 : Nat := 118140960795 + 2427610 * 2 ^ 59
def prefixEnd_2427610 : Nat := 4983230072969 + 3 ^ 40 * 2427610 * 2
def baseEnd_2427610 : Nat := 831020514440901465607087

theorem tailTrace_2427610 : CollatzResearch.WordTrace tailWord_2427610 prefixEnd_2427610 831020514440901465607087 := by
  unfold tailWord_2427610
  simp only [CollatzResearch.WordTrace]
  refine ⟨22135552683797761906224071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59028140490127365083264189 22135552683797761906224071)
  ·
    refine ⟨33203329025696642859336107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22135552683797761906224071 33203329025696642859336107)
    ·
      refine ⟨49804993538544964289004161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33203329025696642859336107 49804993538544964289004161)
      ·
        refine ⟨37353745153908723216753121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49804993538544964289004161 37353745153908723216753121)
        ·
          refine ⟨28015308865431542412564841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37353745153908723216753121 28015308865431542412564841)
          ·
            refine ⟨21011481649073656809423631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28015308865431542412564841 21011481649073656809423631)
            ·
              refine ⟨31517222473610485214135447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21011481649073656809423631 31517222473610485214135447)
              ·
                refine ⟨47275833710415727821203171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31517222473610485214135447 47275833710415727821203171)
                ·
                  refine ⟨70913750565623591731804757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47275833710415727821203171 70913750565623591731804757)
                  ·
                    refine ⟨831020514440901465607087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70913750565623591731804757 831020514440901465607087)
                    ·
                      rfl

theorem cell22_2427610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_2427610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2427610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2427610 prefixEnd_2427610 := by exact prefixLift 2427610
  have htrace : WordTrace (prefixWord ++ tailWord_2427610) baseStart_2427610 baseEnd_2427610 := by
    simpa [prefixWord, tailWord_2427610, baseEnd_2427610] using wordTrace_append hprefix tailTrace_2427610
  have hstable : (prefixWord ++ tailWord_2427610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427610).length < 2 ^ (prefixWord ++ tailWord_2427610).sum := by decide
  have hdescent : baseEnd_2427610 < baseStart_2427610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427629 : List Nat := [1, 5, 1, 2, 1, 1, 3, 2, 3, 3]
def baseStart_2427629 : Nat := 118140960795 + 2427629 * 2 ^ 59
def prefixEnd_2427629 : Nat := 4983230072969 + 3 ^ 40 * 2427629 * 2
def baseEnd_2427629 : Nat := 831027018529191749382029

theorem tailTrace_2427629 : CollatzResearch.WordTrace tailWord_2427629 prefixEnd_2427629 831027018529191749382029 := by
  unfold tailWord_2427629
  simp only [CollatzResearch.WordTrace]
  refine ⟨88542903722122213869837941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59028602481414809246558627 88542903722122213869837941)
  ·
    refine ⟨8300897223948957550297307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88542903722122213869837941 8300897223948957550297307)
    ·
      refine ⟨12451345835923436325445961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8300897223948957550297307 12451345835923436325445961)
      ·
        refine ⟨9338509376942577244084471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12451345835923436325445961 9338509376942577244084471)
        ·
          refine ⟨14007764065413865866126707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9338509376942577244084471 14007764065413865866126707)
          ·
            refine ⟨21011646098120798799190061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14007764065413865866126707 21011646098120798799190061)
            ·
              refine ⟨7879367286795299549696273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21011646098120798799190061 7879367286795299549696273)
              ·
                refine ⟨5909525465096474662272205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7879367286795299549696273 5909525465096474662272205)
                ·
                  refine ⟨2216072049411177998352077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5909525465096474662272205 2216072049411177998352077)
                  ·
                    refine ⟨831027018529191749382029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2216072049411177998352077 831027018529191749382029)
                    ·
                      rfl

theorem cell22_2427629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_2427629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2427629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2427629 prefixEnd_2427629 := by exact prefixLift 2427629
  have htrace : WordTrace (prefixWord ++ tailWord_2427629) baseStart_2427629 baseEnd_2427629 := by
    simpa [prefixWord, tailWord_2427629, baseEnd_2427629] using wordTrace_append hprefix tailTrace_2427629
  have hstable : (prefixWord ++ tailWord_2427629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427629).length < 2 ^ (prefixWord ++ tailWord_2427629).sum := by decide
  have hdescent : baseEnd_2427629 < baseStart_2427629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427640 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 1, 7]
def baseStart_2427640 : Nat := 118140960795 + 2427640 * 2 ^ 59
def prefixEnd_2427640 : Nat := 4983230072969 + 3 ^ 40 * 2427640 * 2
def baseEnd_2427640 : Nat := 831030784053991387356995

theorem tailTrace_2427640 : CollatzResearch.WordTrace tailWord_2427640 prefixEnd_2427640 831030784053991387356995 := by
  unfold tailWord_2427640
  simp only [CollatzResearch.WordTrace]
  refine ⟨44271652462541181374244187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59028869950054908498992249 44271652462541181374244187)
  ·
    refine ⟨66407478693811772061366281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44271652462541181374244187 66407478693811772061366281)
    ·
      refine ⟨49805609020358829046024711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66407478693811772061366281 49805609020358829046024711)
      ·
        refine ⟨74708413530538243569037067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49805609020358829046024711 74708413530538243569037067)
        ·
          refine ⟨112062620295807365353555601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74708413530538243569037067 112062620295807365353555601)
          ·
            refine ⟨84046965221855524015166701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112062620295807365353555601 84046965221855524015166701)
            ·
              refine ⟨31517611958195821505687513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84046965221855524015166701 31517611958195821505687513)
              ·
                refine ⟨23638208968646866129265635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31517611958195821505687513 23638208968646866129265635)
                ·
                  refine ⟨35457313452970299193898453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23638208968646866129265635 35457313452970299193898453)
                  ·
                    refine ⟨831030784053991387356995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35457313452970299193898453 831030784053991387356995)
                    ·
                      rfl

theorem cell22_2427640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_2427640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2427640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2427640 prefixEnd_2427640 := by exact prefixLift 2427640
  have htrace : WordTrace (prefixWord ++ tailWord_2427640) baseStart_2427640 baseEnd_2427640 := by
    simpa [prefixWord, tailWord_2427640, baseEnd_2427640] using wordTrace_append hprefix tailTrace_2427640
  have hstable : (prefixWord ++ tailWord_2427640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427640).length < 2 ^ (prefixWord ++ tailWord_2427640).sum := by decide
  have hdescent : baseEnd_2427640 < baseStart_2427640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427719 : List Nat := [1, 1, 4, 1, 2, 1, 1, 6, 2, 3]
def baseStart_2427719 : Nat := 118140960795 + 2427719 * 2 ^ 59
def prefixEnd_2427719 : Nat := 4983230072969 + 3 ^ 40 * 2427719 * 2
def baseEnd_2427719 : Nat := 831057827368461514631753

theorem tailTrace_2427719 : CollatzResearch.WordTrace tailWord_2427719 prefixEnd_2427719 831057827368461514631753 := by
  unfold tailWord_2427719
  simp only [CollatzResearch.WordTrace]
  refine ⟨88546186291796159240614211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59030790861197439493742807 88546186291796159240614211)
  ·
    refine ⟨132819279437694238860921317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88546186291796159240614211 132819279437694238860921317)
    ·
      refine ⟨24903614894567669786422747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132819279437694238860921317 24903614894567669786422747)
      ·
        refine ⟨37355422341851504679634121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24903614894567669786422747 37355422341851504679634121)
        ·
          refine ⟨28016566756388628509725591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37355422341851504679634121 28016566756388628509725591)
          ·
            refine ⟨42024850134582942764588387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28016566756388628509725591 42024850134582942764588387)
            ·
              refine ⟨63037275201874414146882581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42024850134582942764588387 63037275201874414146882581)
              ·
                refine ⟨2954872275087863163135121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63037275201874414146882581 2954872275087863163135121)
                ·
                  refine ⟨2216154206315897372351341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2954872275087863163135121 2216154206315897372351341)
                  ·
                    refine ⟨831057827368461514631753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2216154206315897372351341 831057827368461514631753)
                    ·
                      rfl

theorem cell22_2427719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_2427719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2427719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2427719 prefixEnd_2427719 := by exact prefixLift 2427719
  have htrace : WordTrace (prefixWord ++ tailWord_2427719) baseStart_2427719 baseEnd_2427719 := by
    simpa [prefixWord, tailWord_2427719, baseEnd_2427719] using wordTrace_append hprefix tailTrace_2427719
  have hstable : (prefixWord ++ tailWord_2427719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427719).length < 2 ^ (prefixWord ++ tailWord_2427719).sum := by decide
  have hdescent : baseEnd_2427719 < baseStart_2427719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427721 : List Nat := [1, 2, 1, 1, 2, 6, 3, 2, 4]
def baseStart_2427721 : Nat := 118140960795 + 2427721 * 2 ^ 59
def prefixEnd_2427721 : Nat := 4983230072969 + 3 ^ 40 * 2427721 * 2
def baseEnd_2427721 : Nat := 277019504003111392027249

theorem tailTrace_2427721 : CollatzResearch.WordTrace tailWord_2427721 prefixEnd_2427721 277019504003111392027249 := by
  unfold tailWord_2427721
  simp only [CollatzResearch.WordTrace]
  refine ⟨88546259237788913582187017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59030839491859275721458011 88546259237788913582187017)
  ·
    refine ⟨66409694428341685186640263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88546259237788913582187017 66409694428341685186640263)
    ·
      refine ⟨99614541642512527779960395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66409694428341685186640263 99614541642512527779960395)
      ·
        refine ⟨149421812463768791669940593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99614541642512527779960395 149421812463768791669940593)
        ·
          refine ⟨112066359347826593752455445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149421812463768791669940593 112066359347826593752455445)
          ·
            refine ⟨5253110594429371582146349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 112066359347826593752455445 5253110594429371582146349)
            ·
              refine ⟨1969916472911014343304881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5253110594429371582146349 1969916472911014343304881)
              ·
                refine ⟨1477437354683260757478661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1969916472911014343304881 1477437354683260757478661)
                ·
                  refine ⟨277019504003111392027249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1477437354683260757478661 277019504003111392027249)
                  ·
                    rfl

theorem cell22_2427721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 2, 4].length) (baseStart_2427721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2427721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2427721 prefixEnd_2427721 := by exact prefixLift 2427721
  have htrace : WordTrace (prefixWord ++ tailWord_2427721) baseStart_2427721 baseEnd_2427721 := by
    simpa [prefixWord, tailWord_2427721, baseEnd_2427721] using wordTrace_append hprefix tailTrace_2427721
  have hstable : (prefixWord ++ tailWord_2427721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427721).length < 2 ^ (prefixWord ++ tailWord_2427721).sum := by decide
  have hdescent : baseEnd_2427721 < baseStart_2427721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427815 : List Nat := [1, 1, 6, 1, 3, 1, 2, 3, 1, 3]
def baseStart_2427815 : Nat := 118140960795 + 2427815 * 2 ^ 59
def prefixEnd_2427815 : Nat := 4983230072969 + 3 ^ 40 * 2427815 * 2
def baseEnd_2427815 : Nat := 831090690130349264231459

theorem tailTrace_2427815 : CollatzResearch.WordTrace tailWord_2427815 prefixEnd_2427815 831090690130349264231459 := by
  unfold tailWord_2427815
  simp only [CollatzResearch.WordTrace]
  refine ⟨88549687699448367636108899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59033125132965578424072599 88549687699448367636108899)
  ·
    refine ⟨132824531549172551454163349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88549687699448367636108899 132824531549172551454163349)
    ·
      refine ⟨6226149916367463349413907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 132824531549172551454163349 6226149916367463349413907)
      ·
        refine ⟨9339224874551195024120861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6226149916367463349413907 9339224874551195024120861)
        ·
          refine ⟨3502209327956698134045323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9339224874551195024120861 3502209327956698134045323)
          ·
            refine ⟨5253313991935047201067985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3502209327956698134045323 5253313991935047201067985)
            ·
              refine ⟨3939985493951285400800989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5253313991935047201067985 3939985493951285400800989)
              ·
                refine ⟨1477494560231732025300371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3939985493951285400800989 1477494560231732025300371)
                ·
                  refine ⟨2216241840347598037950557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1477494560231732025300371 2216241840347598037950557)
                  ·
                    refine ⟨831090690130349264231459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2216241840347598037950557 831090690130349264231459)
                    ·
                      rfl

theorem cell22_2427815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_2427815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2427815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2427815 prefixEnd_2427815 := by exact prefixLift 2427815
  have htrace : WordTrace (prefixWord ++ tailWord_2427815) baseStart_2427815 baseEnd_2427815 := by
    simpa [prefixWord, tailWord_2427815, baseEnd_2427815] using wordTrace_append hprefix tailTrace_2427815
  have hstable : (prefixWord ++ tailWord_2427815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427815).length < 2 ^ (prefixWord ++ tailWord_2427815).sum := by decide
  have hdescent : baseEnd_2427815 < baseStart_2427815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427828 : List Nat := [2, 5, 2, 1, 1, 1, 3, 2, 5]
def baseStart_2427828 : Nat := 118140960795 + 2427828 * 2 ^ 59
def prefixEnd_2427828 : Nat := 4983230072969 + 3 ^ 40 * 2427828 * 2
def baseEnd_2427828 : Nat := 277031713432007187885473

theorem tailTrace_2427828 : CollatzResearch.WordTrace tailWord_2427828 prefixEnd_2427828 277031713432007187885473 := by
  unfold tailWord_2427828
  simp only [CollatzResearch.WordTrace]
  refine ⟨44275080924200635428166069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59033441232267513904221425 44275080924200635428166069)
  ·
    refine ⟨4150788836643809571390569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44275080924200635428166069 4150788836643809571390569)
    ·
      refine ⟨3113091627482857178542927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4150788836643809571390569 3113091627482857178542927)
      ·
        refine ⟨4669637441224285767814391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3113091627482857178542927 4669637441224285767814391)
        ·
          refine ⟨7004456161836428651721587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4669637441224285767814391 7004456161836428651721587)
          ·
            refine ⟨10506684242754642977582381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7004456161836428651721587 10506684242754642977582381)
            ·
              refine ⟨3940006591032991116593393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10506684242754642977582381 3940006591032991116593393)
              ·
                refine ⟨2955004943274743337445045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3940006591032991116593393 2955004943274743337445045)
                ·
                  refine ⟨277031713432007187885473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2955004943274743337445045 277031713432007187885473)
                  ·
                    rfl

theorem cell22_2427828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_2427828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2427828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2427828 prefixEnd_2427828 := by exact prefixLift 2427828
  have htrace : WordTrace (prefixWord ++ tailWord_2427828) baseStart_2427828 baseEnd_2427828 := by
    simpa [prefixWord, tailWord_2427828, baseEnd_2427828] using wordTrace_append hprefix tailTrace_2427828
  have hstable : (prefixWord ++ tailWord_2427828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427828).length < 2 ^ (prefixWord ++ tailWord_2427828).sum := by decide
  have hdescent : baseEnd_2427828 < baseStart_2427828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427858 : List Nat := [3, 2, 2, 3, 1, 2, 2, 2, 1, 4]
def baseStart_2427858 : Nat := 118140960795 + 2427858 * 2 ^ 59
def prefixEnd_2427858 : Nat := 4983230072969 + 3 ^ 40 * 2427858 * 2
def baseEnd_2427858 : Nat := 831105409909111485406327

theorem tailTrace_2427858 : CollatzResearch.WordTrace tailWord_2427858 prefixEnd_2427858 831105409909111485406327 := by
  unfold tailWord_2427858
  simp only [CollatzResearch.WordTrace]
  refine ⟨22137814009573146494981057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59034170692195057319949485 22137814009573146494981057)
  ·
    refine ⟨16603360507179859871235793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22137814009573146494981057 16603360507179859871235793)
    ·
      refine ⟨12452520380384894903426845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16603360507179859871235793 12452520380384894903426845)
      ·
        refine ⟨4669695142644335588785067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12452520380384894903426845 4669695142644335588785067)
        ·
          refine ⟨7004542713966503383177601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4669695142644335588785067 7004542713966503383177601)
          ·
            refine ⟨5253407035474877537383201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7004542713966503383177601 5253407035474877537383201)
            ·
              refine ⟨3940055276606158153037401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5253407035474877537383201 3940055276606158153037401)
              ·
                refine ⟨2955041457454618614778051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3940055276606158153037401 2955041457454618614778051)
                ·
                  refine ⟨4432562186181927922167077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2955041457454618614778051 4432562186181927922167077)
                  ·
                    refine ⟨831105409909111485406327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4432562186181927922167077 831105409909111485406327)
                    ·
                      rfl

theorem cell22_2427858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_2427858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2427858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2427858 prefixEnd_2427858 := by exact prefixLift 2427858
  have htrace : WordTrace (prefixWord ++ tailWord_2427858) baseStart_2427858 baseEnd_2427858 := by
    simpa [prefixWord, tailWord_2427858, baseEnd_2427858] using wordTrace_append hprefix tailTrace_2427858
  have hstable : (prefixWord ++ tailWord_2427858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427858).length < 2 ^ (prefixWord ++ tailWord_2427858).sum := by decide
  have hdescent : baseEnd_2427858 < baseStart_2427858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427890 : List Nat := [3, 2, 1, 5, 2, 1, 1, 1, 6]
def baseStart_2427890 : Nat := 118140960795 + 2427890 * 2 ^ 59
def prefixEnd_2427890 : Nat := 4983230072969 + 3 ^ 40 * 2427890 * 2
def baseEnd_2427890 : Nat := 277038788054358022868743

theorem tailTrace_2427890 : CollatzResearch.WordTrace tailWord_2427890 prefixEnd_2427890 277038788054358022868743 := by
  unfold tailWord_2427890
  simp only [CollatzResearch.WordTrace]
  refine ⟨22138105793544163861272281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59034948782784436963392749 22138105793544163861272281)
  ·
    refine ⟨16603579345158122895954211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22138105793544163861272281 16603579345158122895954211)
    ·
      refine ⟨24905369017737184343931317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16603579345158122895954211 24905369017737184343931317)
      ·
        refine ⟨2334878345412861032243561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24905369017737184343931317 2334878345412861032243561)
        ·
          refine ⟨1751158759059645774182671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2334878345412861032243561 1751158759059645774182671)
          ·
            refine ⟨2626738138589468661274007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1751158759059645774182671 2626738138589468661274007)
            ·
              refine ⟨3940107207884202991911011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2626738138589468661274007 3940107207884202991911011)
              ·
                refine ⟨5910160811826304487866517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3940107207884202991911011 5910160811826304487866517)
                ·
                  refine ⟨277038788054358022868743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5910160811826304487866517 277038788054358022868743)
                  ·
                    rfl

theorem cell22_2427890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_2427890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2427890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2427890 prefixEnd_2427890 := by exact prefixLift 2427890
  have htrace : WordTrace (prefixWord ++ tailWord_2427890) baseStart_2427890 baseEnd_2427890 := by
    simpa [prefixWord, tailWord_2427890, baseEnd_2427890] using wordTrace_append hprefix tailTrace_2427890
  have hstable : (prefixWord ++ tailWord_2427890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427890).length < 2 ^ (prefixWord ++ tailWord_2427890).sum := by decide
  have hdescent : baseEnd_2427890 < baseStart_2427890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427905 : List Nat := [1, 2, 4, 1, 2, 4, 2, 1, 2, 3]
def baseStart_2427905 : Nat := 118140960795 + 2427905 * 2 ^ 59
def prefixEnd_2427905 : Nat := 4983230072969 + 3 ^ 40 * 2427905 * 2
def baseEnd_2427905 : Nat := 831121498969619029481183

theorem tailTrace_2427905 : CollatzResearch.WordTrace tailWord_2427905 prefixEnd_2427905 831121498969619029481183 := by
  unfold tailWord_2427905
  simp only [CollatzResearch.WordTrace]
  refine ⟨88552970269122313006885169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59035313512748208671256779 88552970269122313006885169)
  ·
    refine ⟨66414727701841734755163877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88552970269122313006885169 66414727701841734755163877)
    ·
      refine ⟨12452761444095325266593227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66414727701841734755163877 12452761444095325266593227)
      ·
        refine ⟨18679142166142987899889841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12452761444095325266593227 18679142166142987899889841)
        ·
          refine ⟨14009356624607240924917381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18679142166142987899889841 14009356624607240924917381)
          ·
            refine ⟨2626754367113857673422009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14009356624607240924917381 2626754367113857673422009)
            ·
              refine ⟨1970065775335393255066507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2626754367113857673422009 1970065775335393255066507)
              ·
                refine ⟨2955098663003089882599761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1970065775335393255066507 2955098663003089882599761)
                ·
                  refine ⟨2216323997252317411949821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2955098663003089882599761 2216323997252317411949821)
                  ·
                    refine ⟨831121498969619029481183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2216323997252317411949821 831121498969619029481183)
                    ·
                      rfl

theorem cell22_2427905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_2427905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2427905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2427905 prefixEnd_2427905 := by exact prefixLift 2427905
  have htrace : WordTrace (prefixWord ++ tailWord_2427905) baseStart_2427905 baseEnd_2427905 := by
    simpa [prefixWord, tailWord_2427905, baseEnd_2427905] using wordTrace_append hprefix tailTrace_2427905
  have hstable : (prefixWord ++ tailWord_2427905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427905).length < 2 ^ (prefixWord ++ tailWord_2427905).sum := by decide
  have hdescent : baseEnd_2427905 < baseStart_2427905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427950 : List Nat := [4, 1, 3, 1, 1, 1, 3, 4, 1, 3]
def baseStart_2427950 : Nat := 118140960795 + 2427950 * 2 ^ 59
def prefixEnd_2427950 : Nat := 4983230072969 + 3 ^ 40 * 2427950 * 2
def baseEnd_2427950 : Nat := 831136903389253912106045

theorem tailTrace_2427950 : CollatzResearch.WordTrace tailWord_2427950 prefixEnd_2427950 831136903389253912106045 := by
  unfold tailWord_2427950
  simp only [CollatzResearch.WordTrace]
  refine ⟨11069326444244910711534163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59036407702639523794848869 11069326444244910711534163)
  ·
    refine ⟨16603989666367366067301245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11069326444244910711534163 16603989666367366067301245)
    ·
      refine ⟨6226496124887762275237967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16603989666367366067301245 6226496124887762275237967)
      ·
        refine ⟨9339744187331643412856951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6226496124887762275237967 9339744187331643412856951)
        ·
          refine ⟨14009616280997465119285427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9339744187331643412856951 14009616280997465119285427)
          ·
            refine ⟨21014424421496197678928141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14009616280997465119285427 21014424421496197678928141)
            ·
              refine ⟨7880409158061074129598053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21014424421496197678928141 7880409158061074129598053)
              ·
                refine ⟨1477576717136451399299635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7880409158061074129598053 1477576717136451399299635)
                ·
                  refine ⟨2216365075704677098949453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1477576717136451399299635 2216365075704677098949453)
                  ·
                    refine ⟨831136903389253912106045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2216365075704677098949453 831136903389253912106045)
                    ·
                      rfl

theorem cell22_2427950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_2427950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2427950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2427950 prefixEnd_2427950 := by exact prefixLift 2427950
  have htrace : WordTrace (prefixWord ++ tailWord_2427950) baseStart_2427950 baseEnd_2427950 := by
    simpa [prefixWord, tailWord_2427950, baseEnd_2427950] using wordTrace_append hprefix tailTrace_2427950
  have hstable : (prefixWord ++ tailWord_2427950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427950).length < 2 ^ (prefixWord ++ tailWord_2427950).sum := by decide
  have hdescent : baseEnd_2427950 < baseStart_2427950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427961 : List Nat := [1, 2, 1, 5, 2, 2, 1, 1, 2, 5]
def baseStart_2427961 : Nat := 118140960795 + 2427961 * 2 ^ 59
def prefixEnd_2427961 : Nat := 4983230072969 + 3 ^ 40 * 2427961 * 2
def baseEnd_2427961 : Nat := 831140668914053550081011

theorem tailTrace_2427961 : CollatzResearch.WordTrace tailWord_2427961 prefixEnd_2427961 831140668914053550081011 := by
  unfold tailWord_2427961
  simp only [CollatzResearch.WordTrace]
  refine ⟨88555012756919434570923737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59036675171279623047282491 88555012756919434570923737)
  ·
    refine ⟨66416259567689575928192803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88555012756919434570923737 66416259567689575928192803)
    ·
      refine ⟨99624389351534363892289205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66416259567689575928192803 99624389351534363892289205)
      ·
        refine ⟨9339786501706346614902113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99624389351534363892289205 9339786501706346614902113)
        ·
          refine ⟨7004839876279759961176585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9339786501706346614902113 7004839876279759961176585)
          ·
            refine ⟨5253629907209819970882439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7004839876279759961176585 5253629907209819970882439)
            ·
              refine ⟨7880444860814729956323659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5253629907209819970882439 7880444860814729956323659)
              ·
                refine ⟨11820667291222094934485489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7880444860814729956323659 11820667291222094934485489)
                ·
                  refine ⟨8865500468416571200864117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11820667291222094934485489 8865500468416571200864117)
                  ·
                    refine ⟨831140668914053550081011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8865500468416571200864117 831140668914053550081011)
                    ·
                      rfl

theorem cell22_2427961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 5].length) (baseStart_2427961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2427961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2427961 prefixEnd_2427961 := by exact prefixLift 2427961
  have htrace : WordTrace (prefixWord ++ tailWord_2427961) baseStart_2427961 baseEnd_2427961 := by
    simpa [prefixWord, tailWord_2427961, baseEnd_2427961] using wordTrace_append hprefix tailTrace_2427961
  have hstable : (prefixWord ++ tailWord_2427961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427961).length < 2 ^ (prefixWord ++ tailWord_2427961).sum := by decide
  have hdescent : baseEnd_2427961 < baseStart_2427961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427976 : List Nat := [2, 1, 3, 1, 1, 1, 4, 4, 1, 4]
def baseStart_2427976 : Nat := 118140960795 + 2427976 * 2 ^ 59
def prefixEnd_2427976 : Nat := 4983230072969 + 3 ^ 40 * 2427976 * 2
def baseEnd_2427976 : Nat := 831145803720598510955965

theorem tailTrace_2427976 : CollatzResearch.WordTrace tailWord_2427976 prefixEnd_2427976 831145803720598510955965 := by
  unfold tailWord_2427976
  simp only [CollatzResearch.WordTrace]
  refine ⟨44277779925932546066359891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59037039901243394755146521 44277779925932546066359891)
  ·
    refine ⟨66416669888898819099539837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44277779925932546066359891 66416669888898819099539837)
    ·
      refine ⟨24906251208337057162327439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66416669888898819099539837 24906251208337057162327439)
      ·
        refine ⟨37359376812505585743491159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24906251208337057162327439 37359376812505585743491159)
        ·
          refine ⟨56039065218758378615236739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37359376812505585743491159 56039065218758378615236739)
          ·
            refine ⟨84058597828137567922855109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56039065218758378615236739 84058597828137567922855109)
            ·
              refine ⟨15760987092775793985535333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84058597828137567922855109 15760987092775793985535333)
              ·
                refine ⟨2955185079895461372287875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15760987092775793985535333 2955185079895461372287875)
                ·
                  refine ⟨4432777619843192058431813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2955185079895461372287875 4432777619843192058431813)
                  ·
                    refine ⟨831145803720598510955965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4432777619843192058431813 831145803720598510955965)
                    ·
                      rfl

theorem cell22_2427976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_2427976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2427976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2427976 prefixEnd_2427976 := by exact prefixLift 2427976
  have htrace : WordTrace (prefixWord ++ tailWord_2427976) baseStart_2427976 baseEnd_2427976 := by
    simpa [prefixWord, tailWord_2427976, baseEnd_2427976] using wordTrace_append hprefix tailTrace_2427976
  have hstable : (prefixWord ++ tailWord_2427976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427976).length < 2 ^ (prefixWord ++ tailWord_2427976).sum := by decide
  have hdescent : baseEnd_2427976 < baseStart_2427976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427997 : List Nat := [1, 4, 4, 1, 3, 1, 1, 2, 5]
def baseStart_2427997 : Nat := 118140960795 + 2427997 * 2 ^ 59
def prefixEnd_2427997 : Nat := 4983230072969 + 3 ^ 40 * 2427997 * 2
def baseEnd_2427997 : Nat := 277050997483253818726967

theorem tailTrace_2427997 : CollatzResearch.WordTrace tailWord_2427997 prefixEnd_2427997 277050997483253818726967 := by
  unfold tailWord_2427997
  simp only [CollatzResearch.WordTrace]
  refine ⟨88556325784789012719234245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59037550523192675146156163 88556325784789012719234245)
  ·
    refine ⟨16604311084647939884856421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88556325784789012719234245 16604311084647939884856421)
    ·
      refine ⟨3113308328371488728410579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16604311084647939884856421 3113308328371488728410579)
      ·
        refine ⟨4669962492557233092615869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3113308328371488728410579 4669962492557233092615869)
        ·
          refine ⟨1751235934708962409730951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4669962492557233092615869 1751235934708962409730951)
          ·
            refine ⟨2626853902063443614596427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1751235934708962409730951 2626853902063443614596427)
            ·
              refine ⟨3940280853095165421894641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2626853902063443614596427 3940280853095165421894641)
              ·
                refine ⟨2955210639821374066420981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3940280853095165421894641 2955210639821374066420981)
                ·
                  refine ⟨277050997483253818726967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2955210639821374066420981 277050997483253818726967)
                  ·
                    rfl

theorem cell22_2427997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_2427997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2427997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2427997 prefixEnd_2427997 := by exact prefixLift 2427997
  have htrace : WordTrace (prefixWord ++ tailWord_2427997) baseStart_2427997 baseEnd_2427997 := by
    simpa [prefixWord, tailWord_2427997, baseEnd_2427997] using wordTrace_append hprefix tailTrace_2427997
  have hstable : (prefixWord ++ tailWord_2427997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427997).length < 2 ^ (prefixWord ++ tailWord_2427997).sum := by decide
  have hdescent : baseEnd_2427997 < baseStart_2427997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428036 : List Nat := [2, 3, 2, 1, 2, 3, 1, 8]
def baseStart_2428036 : Nat := 118140960795 + 2428036 * 2 ^ 59
def prefixEnd_2428036 : Nat := 4983230072969 + 3 ^ 40 * 2428036 * 2
def baseEnd_2428036 : Nat := 92351815882975372717309

theorem tailTrace_2428036 : CollatzResearch.WordTrace tailWord_2428036 prefixEnd_2428036 92351815882975372717309 := by
  unfold tailWord_2428036
  simp only [CollatzResearch.WordTrace]
  refine ⟨44278874115823861189951981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59038498821098481586602641 44278874115823861189951981)
  ·
    refine ⟨16604577793433947946231993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44278874115823861189951981 16604577793433947946231993)
    ·
      refine ⟨12453433345075460959673995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16604577793433947946231993 12453433345075460959673995)
      ·
        refine ⟨18680150017613191439510993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12453433345075460959673995 18680150017613191439510993)
        ·
          refine ⟨14010112513209893579633245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18680150017613191439510993 14010112513209893579633245)
          ·
            refine ⟨5253792192453710092362467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14010112513209893579633245 5253792192453710092362467)
            ·
              refine ⟨7880688288680565138543701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5253792192453710092362467 7880688288680565138543701)
              ·
                refine ⟨92351815882975372717309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7880688288680565138543701 92351815882975372717309)
                ·
                  rfl

theorem cell22_2428036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 8].length) (baseStart_2428036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2428036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2428036 prefixEnd_2428036 := by exact prefixLift 2428036
  have htrace : WordTrace (prefixWord ++ tailWord_2428036) baseStart_2428036 baseEnd_2428036 := by
    simpa [prefixWord, tailWord_2428036, baseEnd_2428036] using wordTrace_append hprefix tailTrace_2428036
  have hstable : (prefixWord ++ tailWord_2428036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428036).length < 2 ^ (prefixWord ++ tailWord_2428036).sum := by decide
  have hdescent : baseEnd_2428036 < baseStart_2428036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428051 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 5, 3]
def baseStart_2428051 : Nat := 118140960795 + 2428051 * 2 ^ 59
def prefixEnd_2428051 : Nat := 4983230072969 + 3 ^ 40 * 2428051 * 2
def baseEnd_2428051 : Nat := 831171477753323315330735

theorem tailTrace_2428051 : CollatzResearch.WordTrace tailWord_2428051 prefixEnd_2428051 831171477753323315330735 := by
  unfold tailWord_2428051
  simp only [CollatzResearch.WordTrace]
  refine ⟨88558295326593379941700007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59038863551062253294466671 88558295326593379941700007)
  ·
    refine ⟨132837442989890069912550011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88558295326593379941700007 132837442989890069912550011)
    ·
      refine ⟨199256164484835104868825017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132837442989890069912550011 199256164484835104868825017)
      ·
        refine ⟨149442123363626328651618763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199256164484835104868825017 149442123363626328651618763)
        ·
          refine ⟨224163185045439492977428145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149442123363626328651618763 224163185045439492977428145)
          ·
            refine ⟨168122388784079619733071109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224163185045439492977428145 168122388784079619733071109)
            ·
              refine ⟨31522947897014928699950833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 168122388784079619733071109 31522947897014928699950833)
              ·
                refine ⟨23642210922761196524963125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31522947897014928699950833 23642210922761196524963125)
                ·
                  refine ⟨2216457274008862174215293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23642210922761196524963125 2216457274008862174215293)
                  ·
                    refine ⟨831171477753323315330735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2216457274008862174215293 831171477753323315330735)
                    ·
                      rfl

theorem cell22_2428051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 5, 3].length) (baseStart_2428051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2428051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2428051 prefixEnd_2428051 := by exact prefixLift 2428051
  have htrace : WordTrace (prefixWord ++ tailWord_2428051) baseStart_2428051 baseEnd_2428051 := by
    simpa [prefixWord, tailWord_2428051, baseEnd_2428051] using wordTrace_append hprefix tailTrace_2428051
  have hstable : (prefixWord ++ tailWord_2428051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428051).length < 2 ^ (prefixWord ++ tailWord_2428051).sum := by decide
  have hdescent : baseEnd_2428051 < baseStart_2428051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428074 : List Nat := [3, 1, 5, 1, 1, 3, 2, 1, 2, 3]
def baseStart_2428074 : Nat := 118140960795 + 2428074 * 2 ^ 59
def prefixEnd_2428074 : Nat := 4983230072969 + 3 ^ 40 * 2428074 * 2
def baseEnd_2428074 : Nat := 831179351123358922005665

theorem tailTrace_2428074 : CollatzResearch.WordTrace tailWord_2428074 prefixEnd_2428074 831179351123358922005665 := by
  unfold tailWord_2428074
  simp only [CollatzResearch.WordTrace]
  refine ⟨22139783551377513717446819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59039422803673369913191517 22139783551377513717446819)
  ·
    refine ⟨33209675327066270576170229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22139783551377513717446819 33209675327066270576170229)
    ·
      refine ⟨3113407061912462866515959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33209675327066270576170229 3113407061912462866515959)
      ·
        refine ⟨4670110592868694299773939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3113407061912462866515959 4670110592868694299773939)
        ·
          refine ⟨7005165889303041449660909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4670110592868694299773939 7005165889303041449660909)
          ·
            refine ⟨2626937208488640543622841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7005165889303041449660909 2626937208488640543622841)
            ·
              refine ⟨1970202906366480407717131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2626937208488640543622841 1970202906366480407717131)
              ·
                refine ⟨2955304359549720611575697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1970202906366480407717131 2955304359549720611575697)
                ·
                  refine ⟨2216478269662290458681773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2955304359549720611575697 2216478269662290458681773)
                  ·
                    refine ⟨831179351123358922005665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2216478269662290458681773 831179351123358922005665)
                    ·
                      rfl

theorem cell22_2428074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_2428074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2428074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2428074 prefixEnd_2428074 := by exact prefixLift 2428074
  have htrace : WordTrace (prefixWord ++ tailWord_2428074) baseStart_2428074 baseEnd_2428074 := by
    simpa [prefixWord, tailWord_2428074, baseEnd_2428074] using wordTrace_append hprefix tailTrace_2428074
  have hstable : (prefixWord ++ tailWord_2428074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428074).length < 2 ^ (prefixWord ++ tailWord_2428074).sum := by decide
  have hdescent : baseEnd_2428074 < baseStart_2428074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428143 : List Nat := [1, 1, 2, 1, 7, 1, 1, 2, 6]
def baseStart_2428143 : Nat := 118140960795 + 2428143 * 2 ^ 59
def prefixEnd_2428143 : Nat := 4983230072969 + 3 ^ 40 * 2428143 * 2
def baseEnd_2428143 : Nat := 277067657077821914010151

theorem tailTrace_2428143 : CollatzResearch.WordTrace tailWord_2428143 prefixEnd_2428143 277067657077821914010151 := by
  unfold tailWord_2428143
  simp only [CollatzResearch.WordTrace]
  refine ⟨88561650842260079654049083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59041100561506719769366055 88561650842260079654049083)
  ·
    refine ⟨132842476263390119481073625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88561650842260079654049083 132842476263390119481073625)
    ·
      refine ⟨99631857197542589610805219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132842476263390119481073625 99631857197542589610805219)
      ·
        refine ⟨149447785796313884416207829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99631857197542589610805219 149447785796313884416207829)
        ·
          refine ⟨3502682479601106666004871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 149447785796313884416207829 3502682479601106666004871)
          ·
            refine ⟨5254023719401659999007307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3502682479601106666004871 5254023719401659999007307)
            ·
              refine ⟨7881035579102489998510961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5254023719401659999007307 7881035579102489998510961)
              ·
                refine ⟨5910776684326867498883221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7881035579102489998510961 5910776684326867498883221)
                ·
                  refine ⟨277067657077821914010151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5910776684326867498883221 277067657077821914010151)
                  ·
                    rfl

theorem cell22_2428143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 6].length) (baseStart_2428143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2428143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2428143 prefixEnd_2428143 := by exact prefixLift 2428143
  have htrace : WordTrace (prefixWord ++ tailWord_2428143) baseStart_2428143 baseEnd_2428143 := by
    simpa [prefixWord, tailWord_2428143, baseEnd_2428143] using wordTrace_append hprefix tailTrace_2428143
  have hstable : (prefixWord ++ tailWord_2428143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428143).length < 2 ^ (prefixWord ++ tailWord_2428143).sum := by decide
  have hdescent : baseEnd_2428143 < baseStart_2428143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428162 : List Nat := [3, 4, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_2428162 : Nat := 118140960795 + 2428162 * 2 ^ 59
def prefixEnd_2428162 : Nat := 4983230072969 + 3 ^ 40 * 2428162 * 2
def baseEnd_2428162 : Nat := 831209475321756025805395

theorem tailTrace_2428162 : CollatzResearch.WordTrace tailWord_2428162 prefixEnd_2428162 831209475321756025805395 := by
  unfold tailWord_2428162
  simp only [CollatzResearch.WordTrace]
  refine ⟨22140585957297811474747685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59041562552794163932660493 22140585957297811474747685)
  ·
    refine ⟨4151359866993339651515191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22140585957297811474747685 4151359866993339651515191)
    ·
      refine ⟨6227039800490009477272787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4151359866993339651515191 6227039800490009477272787)
      ·
        refine ⟨9340559700735014215909181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6227039800490009477272787 9340559700735014215909181)
        ·
          refine ⟨3502709887775630330965943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9340559700735014215909181 3502709887775630330965943)
          ·
            refine ⟨5254064831663445496448915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3502709887775630330965943 5254064831663445496448915)
            ·
              refine ⟨7881097247495168244673373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5254064831663445496448915 7881097247495168244673373)
              ·
                refine ⟨2955411467810688091752515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7881097247495168244673373 2955411467810688091752515)
                ·
                  refine ⟨4433117201716032137628773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2955411467810688091752515 4433117201716032137628773)
                  ·
                    refine ⟨831209475321756025805395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4433117201716032137628773 831209475321756025805395)
                    ·
                      rfl

theorem cell22_2428162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_2428162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2428162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2428162 prefixEnd_2428162 := by exact prefixLift 2428162
  have htrace : WordTrace (prefixWord ++ tailWord_2428162) baseStart_2428162 baseEnd_2428162 := by
    simpa [prefixWord, tailWord_2428162, baseEnd_2428162] using wordTrace_append hprefix tailTrace_2428162
  have hstable : (prefixWord ++ tailWord_2428162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428162).length < 2 ^ (prefixWord ++ tailWord_2428162).sum := by decide
  have hdescent : baseEnd_2428162 < baseStart_2428162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428171 : List Nat := [1, 1, 1, 1, 5, 4, 9]
def baseStart_2428171 : Nat := 118140960795 + 2428171 * 2 ^ 59
def prefixEnd_2428171 : Nat := 4983230072969 + 3 ^ 40 * 2428171 * 2
def baseEnd_2428171 : Nat := 30785650229840111197421

theorem tailTrace_2428171 : CollatzResearch.WordTrace tailWord_2428171 prefixEnd_2428171 30785650229840111197421 := by
  unfold tailWord_2428171
  simp only [CollatzResearch.WordTrace]
  refine ⟨88562672086158640436068367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59041781390772426957378911 88562672086158640436068367)
  ·
    refine ⟨132844008129237960654102551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88562672086158640436068367 132844008129237960654102551)
    ·
      refine ⟨199266012193856940981153827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132844008129237960654102551 199266012193856940981153827)
      ·
        refine ⟨298899018290785411471730741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199266012193856940981153827 298899018290785411471730741)
        ·
          refine ⟨28021782964761132325474757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 298899018290785411471730741 28021782964761132325474757)
          ·
            refine ⟨5254084305892712311026517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28021782964761132325474757 5254084305892712311026517)
            ·
              refine ⟨30785650229840111197421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5254084305892712311026517 30785650229840111197421)
              ·
                rfl

theorem cell22_2428171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 9].length) (baseStart_2428171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2428171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2428171 prefixEnd_2428171 := by exact prefixLift 2428171
  have htrace : WordTrace (prefixWord ++ tailWord_2428171) baseStart_2428171 baseEnd_2428171 := by
    simpa [prefixWord, tailWord_2428171, baseEnd_2428171] using wordTrace_append hprefix tailTrace_2428171
  have hstable : (prefixWord ++ tailWord_2428171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428171).length < 2 ^ (prefixWord ++ tailWord_2428171).sum := by decide
  have hdescent : baseEnd_2428171 < baseStart_2428171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428192 : List Nat := [2, 1, 1, 5, 4, 1, 1, 1, 1, 5]
def baseStart_2428192 : Nat := 118140960795 + 2428192 * 2 ^ 59
def prefixEnd_2428192 : Nat := 4983230072969 + 3 ^ 40 * 2428192 * 2
def baseEnd_2428192 : Nat := 831219744934845947555303

theorem tailTrace_2428192 : CollatzResearch.WordTrace tailWord_2428192 prefixEnd_2428192 831219744934845947555303 := by
  unfold tailWord_2428192
  simp only [CollatzResearch.WordTrace]
  refine ⟨44281719009541280511291415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59042292012721707348388553 44281719009541280511291415)
  ·
    refine ⟨66422578514311920766937123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44281719009541280511291415 66422578514311920766937123)
    ·
      refine ⟨99633867771467881150405685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66422578514311920766937123 99633867771467881150405685)
      ·
        refine ⟨9340675103575113857850533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99633867771467881150405685 9340675103575113857850533)
        ·
          refine ⟨1751376581920333848346975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9340675103575113857850533 1751376581920333848346975)
          ·
            refine ⟨2627064872880500772520463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1751376581920333848346975 2627064872880500772520463)
            ·
              refine ⟨3940597309320751158780695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2627064872880500772520463 3940597309320751158780695)
              ·
                refine ⟨5910895963981126738171043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3940597309320751158780695 5910895963981126738171043)
                ·
                  refine ⟨8866343945971690107256565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5910895963981126738171043 8866343945971690107256565)
                  ·
                    refine ⟨831219744934845947555303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8866343945971690107256565 831219744934845947555303)
                    ·
                      rfl

theorem cell22_2428192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 1, 5].length) (baseStart_2428192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2428192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2428192 prefixEnd_2428192 := by exact prefixLift 2428192
  have htrace : WordTrace (prefixWord ++ tailWord_2428192) baseStart_2428192 baseEnd_2428192 := by
    simpa [prefixWord, tailWord_2428192, baseEnd_2428192] using wordTrace_append hprefix tailTrace_2428192
  have hstable : (prefixWord ++ tailWord_2428192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428192).length < 2 ^ (prefixWord ++ tailWord_2428192).sum := by decide
  have hdescent : baseEnd_2428192 < baseStart_2428192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428205 : List Nat := [1, 5, 3, 1, 1, 2, 1, 8]
def baseStart_2428205 : Nat := 118140960795 + 2428205 * 2 ^ 59
def prefixEnd_2428205 : Nat := 4983230072969 + 3 ^ 40 * 2428205 * 2
def baseEnd_2428205 : Nat := 92358243900057582997807

theorem tailTrace_2428205 : CollatzResearch.WordTrace tailWord_2428205 prefixEnd_2428205 92358243900057582997807 := by
  unfold tailWord_2428205
  simp only [CollatzResearch.WordTrace]
  refine ⟨88563912168035464242806069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59042608112023642828537379 88563912168035464242806069)
  ·
    refine ⟨8302866765753324772763069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88563912168035464242806069 8302866765753324772763069)
    ·
      refine ⟨3113575037157496789786151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8302866765753324772763069 3113575037157496789786151)
      ·
        refine ⟨4670362555736245184679227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3113575037157496789786151 4670362555736245184679227)
        ·
          refine ⟨7005543833604367777018841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4670362555736245184679227 7005543833604367777018841)
          ·
            refine ⟨5254157875203275832764131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7005543833604367777018841 5254157875203275832764131)
            ·
              refine ⟨7881236812804913749146197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5254157875203275832764131 7881236812804913749146197)
              ·
                refine ⟨92358243900057582997807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7881236812804913749146197 92358243900057582997807)
                ·
                  rfl

theorem cell22_2428205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 8].length) (baseStart_2428205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2428205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2428205 prefixEnd_2428205 := by exact prefixLift 2428205
  have htrace : WordTrace (prefixWord ++ tailWord_2428205) baseStart_2428205 baseEnd_2428205 := by
    simpa [prefixWord, tailWord_2428205, baseEnd_2428205] using wordTrace_append hprefix tailTrace_2428205
  have hstable : (prefixWord ++ tailWord_2428205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428205).length < 2 ^ (prefixWord ++ tailWord_2428205).sum := by decide
  have hdescent : baseEnd_2428205 < baseStart_2428205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428250 : List Nat := [3, 1, 1, 2, 1, 2, 6, 1, 5]
def baseStart_2428250 : Nat := 118140960795 + 2428250 * 2 ^ 59
def prefixEnd_2428250 : Nat := 4983230072969 + 3 ^ 40 * 2428250 * 2
def baseEnd_2428250 : Nat := 277079866506717709868375

theorem tailTrace_2428250 : CollatzResearch.WordTrace tailWord_2428250 prefixEnd_2428250 277079866506717709868375 := by
  unfold tailWord_2428250
  simp only [CollatzResearch.WordTrace]
  refine ⟨22141388363218109232048551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59043702301914957952129469 22141388363218109232048551)
  ·
    refine ⟨33212082544827163848072827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22141388363218109232048551 33212082544827163848072827)
    ·
      refine ⟨49818123817240745772109241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33212082544827163848072827 49818123817240745772109241)
      ·
        refine ⟨37363592862930559329081931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49818123817240745772109241 37363592862930559329081931)
        ·
          refine ⟨56045389294395838993622897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37363592862930559329081931 56045389294395838993622897)
          ·
            refine ⟨42034041970796879245217173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56045389294395838993622897 42034041970796879245217173)
            ·
              refine ⟨1970345717381103714619555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42034041970796879245217173 1970345717381103714619555)
              ·
                refine ⟨2955518576071655571929333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1970345717381103714619555 2955518576071655571929333)
                ·
                  refine ⟨277079866506717709868375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2955518576071655571929333 277079866506717709868375)
                  ·
                    rfl

theorem cell22_2428250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 5].length) (baseStart_2428250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2428250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2428250 prefixEnd_2428250 := by exact prefixLift 2428250
  have htrace : WordTrace (prefixWord ++ tailWord_2428250) baseStart_2428250 baseEnd_2428250 := by
    simpa [prefixWord, tailWord_2428250, baseEnd_2428250] using wordTrace_append hprefix tailTrace_2428250
  have hstable : (prefixWord ++ tailWord_2428250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428250).length < 2 ^ (prefixWord ++ tailWord_2428250).sum := by decide
  have hdescent : baseEnd_2428250 < baseStart_2428250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428355 : List Nat := [1, 1, 1, 3, 1, 1, 5, 3, 3, 3]
def baseStart_2428355 : Nat := 118140960795 + 2428355 * 2 ^ 59
def prefixEnd_2428355 : Nat := 4983230072969 + 3 ^ 40 * 2428355 * 2
def baseEnd_2428355 : Nat := 831275543165967855729803

theorem tailTrace_2428355 : CollatzResearch.WordTrace tailWord_2428355 prefixEnd_2428355 831275543165967855729803 := by
  unfold tailWord_2428355
  simp only [CollatzResearch.WordTrace]
  refine ⟨88569383117492039860766519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59046255411661359907177679 88569383117492039860766519)
  ·
    refine ⟨132854074676238059791149779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88569383117492039860766519 132854074676238059791149779)
    ·
      refine ⟨199281112014357089686724669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132854074676238059791149779 199281112014357089686724669)
      ·
        refine ⟨74730417005383908632521751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199281112014357089686724669 74730417005383908632521751)
        ·
          refine ⟨112095625508075862948782627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74730417005383908632521751 112095625508075862948782627)
          ·
            refine ⟨168143438262113794423173941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112095625508075862948782627 168143438262113794423173941)
            ·
              refine ⟨15763447337073168227172557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 168143438262113794423173941 15763447337073168227172557)
              ·
                refine ⟨5911292751402438085189709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15763447337073168227172557 5911292751402438085189709)
                ·
                  refine ⟨2216734781775914281946141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5911292751402438085189709 2216734781775914281946141)
                  ·
                    refine ⟨831275543165967855729803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2216734781775914281946141 831275543165967855729803)
                    ·
                      rfl

theorem cell22_2428355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 3, 3].length) (baseStart_2428355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2428355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2428355 prefixEnd_2428355 := by exact prefixLift 2428355
  have htrace : WordTrace (prefixWord ++ tailWord_2428355) baseStart_2428355 baseEnd_2428355 := by
    simpa [prefixWord, tailWord_2428355, baseEnd_2428355] using wordTrace_append hprefix tailTrace_2428355
  have hstable : (prefixWord ++ tailWord_2428355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428355).length < 2 ^ (prefixWord ++ tailWord_2428355).sum := by decide
  have hdescent : baseEnd_2428355 < baseStart_2428355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428374 : List Nat := [5, 2, 1, 1, 1, 4, 2, 6]
def baseStart_2428374 : Nat := 118140960795 + 2428374 * 2 ^ 59
def prefixEnd_2428374 : Nat := 4983230072969 + 3 ^ 40 * 2428374 * 2
def baseEnd_2428374 : Nat := 92364671917139793278305

theorem tailTrace_2428374 : CollatzResearch.WordTrace tailWord_2428374 prefixEnd_2428374 92364671917139793278305 := by
  unfold tailWord_2428374
  simp only [CollatzResearch.WordTrace]
  refine ⟨5535629756526450381606761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59046717402948804070472117 5535629756526450381606761)
  ·
    refine ⟨4151722317394837786205071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5535629756526450381606761 4151722317394837786205071)
    ·
      refine ⟨6227583476092256679307607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4151722317394837786205071 6227583476092256679307607)
      ·
        refine ⟨9341375214138385018961411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6227583476092256679307607 9341375214138385018961411)
        ·
          refine ⟨14012062821207577528442117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9341375214138385018961411 14012062821207577528442117)
          ·
            refine ⟨2627261778976420786582897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14012062821207577528442117 2627261778976420786582897)
            ·
              refine ⟨1970446334232315589937173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2627261778976420786582897 1970446334232315589937173)
              ·
                refine ⟨92364671917139793278305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1970446334232315589937173 92364671917139793278305)
                ·
                  rfl

theorem cell22_2428374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_2428374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2428374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2428374 prefixEnd_2428374 := by exact prefixLift 2428374
  have htrace : WordTrace (prefixWord ++ tailWord_2428374) baseStart_2428374 baseEnd_2428374 := by
    simpa [prefixWord, tailWord_2428374, baseEnd_2428374] using wordTrace_append hprefix tailTrace_2428374
  have hstable : (prefixWord ++ tailWord_2428374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428374).length < 2 ^ (prefixWord ++ tailWord_2428374).sum := by decide
  have hdescent : baseEnd_2428374 < baseStart_2428374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428449 : List Nat := [1, 2, 3, 2, 2, 3, 3, 1, 1, 4]
def baseStart_2428449 : Nat := 118140960795 + 2428449 * 2 ^ 59
def prefixEnd_2428449 : Nat := 4983230072969 + 3 ^ 40 * 2428449 * 2
def baseEnd_2428449 : Nat := 831307721286982943879515

theorem tailTrace_2428449 : CollatzResearch.WordTrace tailWord_2428449 prefixEnd_2428449 831307721286982943879515 := by
  unfold tailWord_2428449
  simp only [CollatzResearch.WordTrace]
  refine ⟨88572811579151493914688401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59048541052767662609792267 88572811579151493914688401)
  ·
    refine ⟨66429608684363620436016301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88572811579151493914688401 66429608684363620436016301)
    ·
      refine ⟨24911103256636357663506113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66429608684363620436016301 24911103256636357663506113)
      ·
        refine ⟨18683327442477268247629585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24911103256636357663506113 18683327442477268247629585)
        ·
          refine ⟨14012495581857951185722189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18683327442477268247629585 14012495581857951185722189)
          ·
            refine ⟨5254685843196731694645821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14012495581857951185722189 5254685843196731694645821)
            ·
              refine ⟨1970507191198774385492183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5254685843196731694645821 1970507191198774385492183)
              ·
                refine ⟨2955760786798161578238275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1970507191198774385492183 2955760786798161578238275)
                ·
                  refine ⟨4433641180197242367357413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2955760786798161578238275 4433641180197242367357413)
                  ·
                    refine ⟨831307721286982943879515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4433641180197242367357413 831307721286982943879515)
                    ·
                      rfl

theorem cell22_2428449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_2428449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2428449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2428449 prefixEnd_2428449 := by exact prefixLift 2428449
  have htrace : WordTrace (prefixWord ++ tailWord_2428449) baseStart_2428449 baseEnd_2428449 := by
    simpa [prefixWord, tailWord_2428449, baseEnd_2428449] using wordTrace_append hprefix tailTrace_2428449
  have hstable : (prefixWord ++ tailWord_2428449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428449).length < 2 ^ (prefixWord ++ tailWord_2428449).sum := by decide
  have hdescent : baseEnd_2428449 < baseStart_2428449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428492 : List Nat := [2, 2, 1, 3, 1, 4, 3, 6]
def baseStart_2428492 : Nat := 118140960795 + 2428492 * 2 ^ 59
def prefixEnd_2428492 : Nat := 4983230072969 + 3 ^ 40 * 2428492 * 2
def baseEnd_2428492 : Nat := 92369160118416129450487

theorem tailTrace_2428492 : CollatzResearch.WordTrace tailWord_2428492 prefixEnd_2428492 92369160118416129450487 := by
  unfold tailWord_2428492
  simp only [CollatzResearch.WordTrace]
  refine ⟨44287189958997856129251865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59049586611997141505669153 44287189958997856129251865)
  ·
    refine ⟨33215392469248392096938899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44287189958997856129251865 33215392469248392096938899)
    ·
      refine ⟨49823088703872588145408349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33215392469248392096938899 49823088703872588145408349)
      ·
        refine ⟨18683658263952220554528131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49823088703872588145408349 18683658263952220554528131)
        ·
          refine ⟨28025487395928330831792197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18683658263952220554528131 28025487395928330831792197)
          ·
            refine ⟨5254778886736562030961037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28025487395928330831792197 5254778886736562030961037)
            ·
              refine ⟨1970542082526210761610389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5254778886736562030961037 1970542082526210761610389)
              ·
                refine ⟨92369160118416129450487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1970542082526210761610389 92369160118416129450487)
                ·
                  rfl

theorem cell22_2428492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 6].length) (baseStart_2428492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2428492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2428492 prefixEnd_2428492 := by exact prefixLift 2428492
  have htrace : WordTrace (prefixWord ++ tailWord_2428492) baseStart_2428492 baseEnd_2428492 := by
    simpa [prefixWord, tailWord_2428492, baseEnd_2428492] using wordTrace_append hprefix tailTrace_2428492
  have hstable : (prefixWord ++ tailWord_2428492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428492).length < 2 ^ (prefixWord ++ tailWord_2428492).sum := by decide
  have hdescent : baseEnd_2428492 < baseStart_2428492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428509 : List Nat := [1, 4, 4, 2, 1, 1, 9]
def baseStart_2428509 : Nat := 118140960795 + 2428509 * 2 ^ 59
def prefixEnd_2428509 : Nat := 4983230072969 + 3 ^ 40 * 2428509 * 2
def baseEnd_2428509 : Nat := 30789935574561584717753

theorem tailTrace_2428509 : CollatzResearch.WordTrace tailWord_2428509 prefixEnd_2428509 30789935574561584717753 := by
  unfold tailWord_2428509
  simp only [CollatzResearch.WordTrace]
  refine ⟨88574999958934124161872581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59049999972622749441248387 88574999958934124161872581)
  ·
    refine ⟨16607812492300148280351109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88574999958934124161872581 16607812492300148280351109)
    ·
      refine ⟨3113964842306277802565833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16607812492300148280351109 3113964842306277802565833)
      ·
        refine ⟨2335473631729708351924375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3113964842306277802565833 2335473631729708351924375)
        ·
          refine ⟨3503210447594562527886563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2335473631729708351924375 3503210447594562527886563)
          ·
            refine ⟨5254815671391843791829845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3503210447594562527886563 5254815671391843791829845)
            ·
              refine ⟨30789935574561584717753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5254815671391843791829845 30789935574561584717753)
              ·
                rfl

theorem cell22_2428509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 9].length) (baseStart_2428509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2428509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2428509 prefixEnd_2428509 := by exact prefixLift 2428509
  have htrace : WordTrace (prefixWord ++ tailWord_2428509) baseStart_2428509 baseEnd_2428509 := by
    simpa [prefixWord, tailWord_2428509, baseEnd_2428509] using wordTrace_append hprefix tailTrace_2428509
  have hstable : (prefixWord ++ tailWord_2428509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428509).length < 2 ^ (prefixWord ++ tailWord_2428509).sum := by decide
  have hdescent : baseEnd_2428509 < baseStart_2428509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428558 : List Nat := [4, 1, 1, 3, 1, 4, 1, 3, 1, 3]
def baseStart_2428558 : Nat := 118140960795 + 2428558 * 2 ^ 59
def prefixEnd_2428558 : Nat := 4983230072969 + 3 ^ 40 * 2428558 * 2
def baseEnd_2428558 : Nat := 831345034214542992904181

theorem tailTrace_2428558 : CollatzResearch.WordTrace tailWord_2428558 prefixEnd_2428558 831345034214542992904181 := by
  unfold tailWord_2428558
  simp only [CollatzResearch.WordTrace]
  refine ⟨11072098391969575691300791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59051191423837737020270885 11072098391969575691300791)
  ·
    refine ⟨16608147587954363536951187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11072098391969575691300791 16608147587954363536951187)
    ·
      refine ⟨24912221381931545305426781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16608147587954363536951187 24912221381931545305426781)
      ·
        refine ⟨9342083018224329489535043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24912221381931545305426781 9342083018224329489535043)
        ·
          refine ⟨14013124527336494234302565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9342083018224329489535043 14013124527336494234302565)
          ·
            refine ⟨2627460848875592668931731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14013124527336494234302565 2627460848875592668931731)
            ·
              refine ⟨3941191273313389003397597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2627460848875592668931731 3941191273313389003397597)
              ·
                refine ⟨1477946727492520876274099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3941191273313389003397597 1477946727492520876274099)
                ·
                  refine ⟨2216920091238781314411149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1477946727492520876274099 2216920091238781314411149)
                  ·
                    refine ⟨831345034214542992904181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2216920091238781314411149 831345034214542992904181)
                    ·
                      rfl

theorem cell22_2428558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_2428558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2428558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2428558 prefixEnd_2428558 := by exact prefixLift 2428558
  have htrace : WordTrace (prefixWord ++ tailWord_2428558) baseStart_2428558 baseEnd_2428558 := by
    simpa [prefixWord, tailWord_2428558, baseEnd_2428558] using wordTrace_append hprefix tailTrace_2428558
  have hstable : (prefixWord ++ tailWord_2428558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428558).length < 2 ^ (prefixWord ++ tailWord_2428558).sum := by decide
  have hdescent : baseEnd_2428558 < baseStart_2428558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428565 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 8]
def baseStart_2428565 : Nat := 118140960795 + 2428565 * 2 ^ 59
def prefixEnd_2428565 : Nat := 4983230072969 + 3 ^ 40 * 2428565 * 2
def baseEnd_2428565 : Nat := 277115810152532435993053

theorem tailTrace_2428565 : CollatzResearch.WordTrace tailWord_2428565 prefixEnd_2428565 277115810152532435993053 := by
  unfold tailWord_2428565
  simp only [CollatzResearch.WordTrace]
  refine ⟨88577042446731245725911149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59051361631154163817274099 88577042446731245725911149)
  ·
    refine ⟨33216390917524217147216681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88577042446731245725911149 33216390917524217147216681)
    ·
      refine ⟨24912293188143162860412511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33216390917524217147216681 24912293188143162860412511)
      ·
        refine ⟨37368439782214744290618767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24912293188143162860412511 37368439782214744290618767)
        ·
          refine ⟨56052659673322116435928151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37368439782214744290618767 56052659673322116435928151)
          ·
            refine ⟨84078989509983174653892227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56052659673322116435928151 84078989509983174653892227)
            ·
              refine ⟨126118484264974761980838341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84078989509983174653892227 126118484264974761980838341)
              ·
                refine ⟨23647215799682767871407189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126118484264974761980838341 23647215799682767871407189)
                ·
                  refine ⟨277115810152532435993053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23647215799682767871407189 277115810152532435993053)
                  ·
                    rfl

theorem cell22_2428565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 8].length) (baseStart_2428565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2428565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2428565 prefixEnd_2428565 := by exact prefixLift 2428565
  have htrace : WordTrace (prefixWord ++ tailWord_2428565) baseStart_2428565 baseEnd_2428565 := by
    simpa [prefixWord, tailWord_2428565, baseEnd_2428565] using wordTrace_append hprefix tailTrace_2428565
  have hstable : (prefixWord ++ tailWord_2428565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428565).length < 2 ^ (prefixWord ++ tailWord_2428565).sum := by decide
  have hdescent : baseEnd_2428565 < baseStart_2428565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428575 : List Nat := [1, 1, 2, 7, 1, 1, 3, 2, 1, 3]
def baseStart_2428575 : Nat := 118140960795 + 2428575 * 2 ^ 59
def prefixEnd_2428575 : Nat := 4983230072969 + 3 ^ 40 * 2428575 * 2
def baseEnd_2428575 : Nat := 831350853661960615229129

theorem tailTrace_2428575 : CollatzResearch.WordTrace tailWord_2428575 prefixEnd_2428575 831350853661960615229129 := by
  unfold tailWord_2428575
  simp only [CollatzResearch.WordTrace]
  refine ⟨88577407176695017433775179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59051604784463344955850119 88577407176695017433775179)
  ·
    refine ⟨132866110765042526150662769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88577407176695017433775179 132866110765042526150662769)
    ·
      refine ⟨99649583073781894612997077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132866110765042526150662769 99649583073781894612997077)
      ·
        refine ⟨2335537103291763154992119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 99649583073781894612997077 2335537103291763154992119)
        ·
          refine ⟨3503305654937644732488179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2335537103291763154992119 3503305654937644732488179)
          ·
            refine ⟨5254958482406467098732269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3503305654937644732488179 5254958482406467098732269)
            ·
              refine ⟨1970609430902425162024601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5254958482406467098732269 1970609430902425162024601)
              ·
                refine ⟨1477957073176818871518451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1970609430902425162024601 1477957073176818871518451)
                ·
                  refine ⟨2216935609765228307277677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1477957073176818871518451 2216935609765228307277677)
                  ·
                    refine ⟨831350853661960615229129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2216935609765228307277677 831350853661960615229129)
                    ·
                      rfl

theorem cell22_2428575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 2, 1, 3].length) (baseStart_2428575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2428575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2428575 prefixEnd_2428575 := by exact prefixLift 2428575
  have htrace : WordTrace (prefixWord ++ tailWord_2428575) baseStart_2428575 baseEnd_2428575 := by
    simpa [prefixWord, tailWord_2428575, baseEnd_2428575] using wordTrace_append hprefix tailTrace_2428575
  have hstable : (prefixWord ++ tailWord_2428575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428575).length < 2 ^ (prefixWord ++ tailWord_2428575).sum := by decide
  have hdescent : baseEnd_2428575 < baseStart_2428575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428706 : List Nat := [3, 3, 1, 1, 2, 1, 5, 1, 5]
def baseStart_2428706 : Nat := 118140960795 + 2428706 * 2 ^ 59
def prefixEnd_2428706 : Nat := 4983230072969 + 3 ^ 40 * 2428706 * 2
def baseEnd_2428706 : Nat := 277131899213039980067909

theorem tailTrace_2428706 : CollatzResearch.WordTrace tailWord_2428706 prefixEnd_2428706 277131899213039980067909 := by
  unfold tailWord_2428706
  simp only [CollatzResearch.WordTrace]
  refine ⟨22145546284805106701698493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59054790092813617871195981 22145546284805106701698493)
  ·
    refine ⟨8304579856801915013136935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22145546284805106701698493 8304579856801915013136935)
    ·
      refine ⟨12456869785202872519705403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8304579856801915013136935 12456869785202872519705403)
      ·
        refine ⟨18685304677804308779558105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12456869785202872519705403 18685304677804308779558105)
        ·
          refine ⟨14013978508353231584668579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18685304677804308779558105 14013978508353231584668579)
          ·
            refine ⟨21020967762529847377002869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14013978508353231584668579 21020967762529847377002869)
            ·
              refine ⟨1970715727737173191594019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21020967762529847377002869 1970715727737173191594019)
              ·
                refine ⟨2956073591605759787391029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1970715727737173191594019 2956073591605759787391029)
                ·
                  refine ⟨277131899213039980067909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2956073591605759787391029 277131899213039980067909)
                  ·
                    rfl

theorem cell22_2428706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_2428706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2428706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2428706 prefixEnd_2428706 := by exact prefixLift 2428706
  have htrace : WordTrace (prefixWord ++ tailWord_2428706) baseStart_2428706 baseEnd_2428706 := by
    simpa [prefixWord, tailWord_2428706, baseEnd_2428706] using wordTrace_append hprefix tailTrace_2428706
  have hstable : (prefixWord ++ tailWord_2428706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428706).length < 2 ^ (prefixWord ++ tailWord_2428706).sum := by decide
  have hdescent : baseEnd_2428706 < baseStart_2428706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428777 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 2, 7]
def baseStart_2428777 : Nat := 118140960795 + 2428777 * 2 ^ 59
def prefixEnd_2428777 : Nat := 4983230072969 + 3 ^ 40 * 2428777 * 2
def baseEnd_2428777 : Nat := 831420002390099421678509

theorem tailTrace_2428777 : CollatzResearch.WordTrace tailWord_2428777 prefixEnd_2428777 831420002390099421678509 := by
  unfold tailWord_2428777
  simp only [CollatzResearch.WordTrace]
  refine ⟨88584774721963205932628585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59056516481308803955085723 88584774721963205932628585)
  ·
    refine ⟨66438581041472404449471439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88584774721963205932628585 66438581041472404449471439)
    ·
      refine ⟨99657871562208606674207159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66438581041472404449471439 99657871562208606674207159)
      ·
        refine ⟨149486807343312910011310739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99657871562208606674207159 149486807343312910011310739)
        ·
          refine ⟨224230211014969365016966109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149486807343312910011310739 224230211014969365016966109)
          ·
            refine ⟨84086329130613511881362291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 224230211014969365016966109 84086329130613511881362291)
            ·
              refine ⟨126129493695920267822043437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84086329130613511881362291 126129493695920267822043437)
              ·
                refine ⟨47298560135970100433266289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126129493695920267822043437 47298560135970100433266289)
                ·
                  refine ⟨35473920101977575324949717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47298560135970100433266289 35473920101977575324949717)
                  ·
                    refine ⟨831420002390099421678509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35473920101977575324949717 831420002390099421678509)
                    ·
                      rfl

theorem cell22_2428777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 7].length) (baseStart_2428777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2428777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2428777 prefixEnd_2428777 := by exact prefixLift 2428777
  have htrace : WordTrace (prefixWord ++ tailWord_2428777) baseStart_2428777 baseEnd_2428777 := by
    simpa [prefixWord, tailWord_2428777, baseEnd_2428777] using wordTrace_append hprefix tailTrace_2428777
  have hstable : (prefixWord ++ tailWord_2428777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428777).length < 2 ^ (prefixWord ++ tailWord_2428777).sum := by decide
  have hdescent : baseEnd_2428777 < baseStart_2428777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428798 : List Nat := [4, 2, 3, 1, 1, 1, 2, 2, 2, 4]
def baseStart_2428798 : Nat := 118140960795 + 2428798 * 2 ^ 59
def prefixEnd_2428798 : Nat := 4983230072969 + 3 ^ 40 * 2428798 * 2
def baseEnd_2428798 : Nat := 831427191119262366903445

theorem tailTrace_2428798 : CollatzResearch.WordTrace tailWord_2428798 prefixEnd_2428798 831427191119262366903445 := by
  unfold tailWord_2428798
  simp only [CollatzResearch.WordTrace]
  refine ⟨11073192581860890814892881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59057027103258084346095365 11073192581860890814892881)
  ·
    refine ⟨8304894436395668111169661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11073192581860890814892881 8304894436395668111169661)
    ·
      refine ⟨3114335413648375541688623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8304894436395668111169661 3114335413648375541688623)
      ·
        refine ⟨4671503120472563312532935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3114335413648375541688623 4671503120472563312532935)
        ·
          refine ⟨7007254680708844968799403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4671503120472563312532935 7007254680708844968799403)
          ·
            refine ⟨10510882021063267453199105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7007254680708844968799403 10510882021063267453199105)
            ·
              refine ⟨7883161515797450589899329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10510882021063267453199105 7883161515797450589899329)
              ·
                refine ⟨5912371136848087942424497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7883161515797450589899329 5912371136848087942424497)
                ·
                  refine ⟨4434278352636065956818373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5912371136848087942424497 4434278352636065956818373)
                  ·
                    refine ⟨831427191119262366903445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4434278352636065956818373 831427191119262366903445)
                    ·
                      rfl

theorem cell22_2428798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_2428798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2428798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2428798 prefixEnd_2428798 := by exact prefixLift 2428798
  have htrace : WordTrace (prefixWord ++ tailWord_2428798) baseStart_2428798 baseEnd_2428798 := by
    simpa [prefixWord, tailWord_2428798, baseEnd_2428798] using wordTrace_append hprefix tailTrace_2428798
  have hstable : (prefixWord ++ tailWord_2428798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428798).length < 2 ^ (prefixWord ++ tailWord_2428798).sum := by decide
  have hdescent : baseEnd_2428798 < baseStart_2428798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428828 : List Nat := [2, 2, 3, 3, 1, 2, 1, 2, 3, 3]
def baseStart_2428828 : Nat := 118140960795 + 2428828 * 2 ^ 59
def prefixEnd_2428828 : Nat := 4983230072969 + 3 ^ 40 * 2428828 * 2
def baseEnd_2428828 : Nat := 831437460732352288653353

theorem tailTrace_2428828 : CollatzResearch.WordTrace tailWord_2428828 prefixEnd_2428828 831437460732352288653353 := by
  unfold tailWord_2428828
  simp only [CollatzResearch.WordTrace]
  refine ⟨44293317422389220821367569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59057756563185627761823425 44293317422389220821367569)
  ·
    refine ⟨33219988066791915616025677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44293317422389220821367569 33219988066791915616025677)
    ·
      refine ⟨12457495525046968356009629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33219988066791915616025677 12457495525046968356009629)
      ·
        refine ⟨4671560821892613133503611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12457495525046968356009629 4671560821892613133503611)
        ·
          refine ⟨7007341232838919700255417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4671560821892613133503611 7007341232838919700255417)
          ·
            refine ⟨5255505924629189775191563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7007341232838919700255417 5255505924629189775191563)
            ·
              refine ⟨7883258886943784662787345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5255505924629189775191563 7883258886943784662787345)
              ·
                refine ⟨5912444165207838497090509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7883258886943784662787345 5912444165207838497090509)
                ·
                  refine ⟨2217166561952939436408941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5912444165207838497090509 2217166561952939436408941)
                  ·
                    refine ⟨831437460732352288653353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2217166561952939436408941 831437460732352288653353)
                    ·
                      rfl

theorem cell22_2428828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_2428828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2428828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2428828 prefixEnd_2428828 := by exact prefixLift 2428828
  have htrace : WordTrace (prefixWord ++ tailWord_2428828) baseStart_2428828 baseEnd_2428828 := by
    simpa [prefixWord, tailWord_2428828, baseEnd_2428828] using wordTrace_append hprefix tailTrace_2428828
  have hstable : (prefixWord ++ tailWord_2428828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428828).length < 2 ^ (prefixWord ++ tailWord_2428828).sum := by decide
  have hdescent : baseEnd_2428828 < baseStart_2428828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428830 : List Nat := [4, 3, 1, 3, 1, 1, 3, 6]
def baseStart_2428830 : Nat := 118140960795 + 2428830 * 2 ^ 59
def prefixEnd_2428830 : Nat := 4983230072969 + 3 ^ 40 * 2428830 * 2
def baseEnd_2428830 : Nat := 92382016152580550011483

theorem tailTrace_2428830 : CollatzResearch.WordTrace tailWord_2428830 prefixEnd_2428830 92382016152580550011483 := by
  unfold tailWord_2428830
  simp only [CollatzResearch.WordTrace]
  refine ⟨11073338473846399498038493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59057805193847463989538629 11073338473846399498038493)
  ·
    refine ⟨4152501927692399811764435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11073338473846399498038493 4152501927692399811764435)
    ·
      refine ⟨6228752891538599717646653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4152501927692399811764435 6228752891538599717646653)
      ·
        refine ⟨2335782334326974894117495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6228752891538599717646653 2335782334326974894117495)
        ·
          refine ⟨3503673501490462341176243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2335782334326974894117495 3503673501490462341176243)
          ·
            refine ⟨5255510252235693511764365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3503673501490462341176243 5255510252235693511764365)
            ·
              refine ⟨1970816344588385066911637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5255510252235693511764365 1970816344588385066911637)
              ·
                refine ⟨92382016152580550011483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1970816344588385066911637 92382016152580550011483)
                ·
                  rfl

theorem cell22_2428830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 6].length) (baseStart_2428830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2428830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2428830 prefixEnd_2428830 := by exact prefixLift 2428830
  have htrace : WordTrace (prefixWord ++ tailWord_2428830) baseStart_2428830 baseEnd_2428830 := by
    simpa [prefixWord, tailWord_2428830, baseEnd_2428830] using wordTrace_append hprefix tailTrace_2428830
  have hstable : (prefixWord ++ tailWord_2428830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428830).length < 2 ^ (prefixWord ++ tailWord_2428830).sum := by decide
  have hdescent : baseEnd_2428830 < baseStart_2428830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428935 : List Nat := [1, 1, 4, 3, 1, 2, 4, 1, 2, 3]
def baseStart_2428935 : Nat := 118140960795 + 2428935 * 2 ^ 59
def prefixEnd_2428935 : Nat := 4983230072969 + 3 ^ 40 * 2428935 * 2
def baseEnd_2428935 : Nat := 831474089019039676228025

theorem tailTrace_2428935 : CollatzResearch.WordTrace tailWord_2428935 prefixEnd_2428935 831474089019039676228025 := by
  unfold tailWord_2428935
  simp only [CollatzResearch.WordTrace]
  refine ⟨88590537455390798916880259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59060358303593865944586839 88590537455390798916880259)
  ·
    refine ⟨132885806183086198375320389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88590537455390798916880259 132885806183086198375320389)
    ·
      refine ⟨24916088659328662195372573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132885806183086198375320389 24916088659328662195372573)
      ·
        refine ⟨9343533247248248323264715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24916088659328662195372573 9343533247248248323264715)
        ·
          refine ⟨14015299870872372484897073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9343533247248248323264715 14015299870872372484897073)
          ·
            refine ⟨10511474903154279363672805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14015299870872372484897073 10511474903154279363672805)
            ·
              refine ⟨1970901544341427380688651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10511474903154279363672805 1970901544341427380688651)
              ·
                refine ⟨2956352316512141071032977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1970901544341427380688651 2956352316512141071032977)
                ·
                  refine ⟨2217264237384105803274733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2956352316512141071032977 2217264237384105803274733)
                  ·
                    refine ⟨831474089019039676228025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2217264237384105803274733 831474089019039676228025)
                    ·
                      rfl

theorem cell22_2428935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_2428935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2428935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2428935 prefixEnd_2428935 := by exact prefixLift 2428935
  have htrace : WordTrace (prefixWord ++ tailWord_2428935) baseStart_2428935 baseEnd_2428935 := by
    simpa [prefixWord, tailWord_2428935, baseEnd_2428935] using wordTrace_append hprefix tailTrace_2428935
  have hstable : (prefixWord ++ tailWord_2428935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428935).length < 2 ^ (prefixWord ++ tailWord_2428935).sum := by decide
  have hdescent : baseEnd_2428935 < baseStart_2428935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428944 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 2, 6]
def baseStart_2428944 : Nat := 118140960795 + 2428944 * 2 ^ 59
def prefixEnd_2428944 : Nat := 4983230072969 + 3 ^ 40 * 2428944 * 2
def baseEnd_2428944 : Nat := 831477169902966652752997

theorem tailTrace_2428944 : CollatzResearch.WordTrace tailWord_2428944 prefixEnd_2428944 831477169902966652752997 := by
  unfold tailWord_2428944
  simp only [CollatzResearch.WordTrace]
  refine ⟨44295432856179096726978943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59060577141572128969305257 44295432856179096726978943)
  ·
    refine ⟨66443149284268645090468415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44295432856179096726978943 66443149284268645090468415)
    ·
      refine ⟨99664723926402967635702623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66443149284268645090468415 99664723926402967635702623)
      ·
        refine ⟨149497085889604451453553935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99664723926402967635702623 149497085889604451453553935)
        ·
          refine ⟨224245628834406677180330903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149497085889604451453553935 224245628834406677180330903)
          ·
            refine ⟨336368443251610015770496355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224245628834406677180330903 336368443251610015770496355)
            ·
              refine ⟨504552664877415023655744533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336368443251610015770496355 504552664877415023655744533)
              ·
                refine ⟨23650906166128829233863025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 504552664877415023655744533 23650906166128829233863025)
                ·
                  refine ⟨17738179624596621925397269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23650906166128829233863025 17738179624596621925397269)
                  ·
                    refine ⟨831477169902966652752997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17738179624596621925397269 831477169902966652752997)
                    ·
                      rfl

theorem cell22_2428944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 2, 6].length) (baseStart_2428944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2428944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2428944 prefixEnd_2428944 := by exact prefixLift 2428944
  have htrace : WordTrace (prefixWord ++ tailWord_2428944) baseStart_2428944 baseEnd_2428944 := by
    simpa [prefixWord, tailWord_2428944, baseEnd_2428944] using wordTrace_append hprefix tailTrace_2428944
  have hstable : (prefixWord ++ tailWord_2428944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428944).length < 2 ^ (prefixWord ++ tailWord_2428944).sum := by decide
  have hdescent : baseEnd_2428944 < baseStart_2428944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428976 : List Nat := [2, 1, 1, 1, 2, 5, 1, 4, 5]
def baseStart_2428976 : Nat := 118140960795 + 2428976 * 2 ^ 59
def prefixEnd_2428976 : Nat := 4983230072969 + 3 ^ 40 * 2428976 * 2
def baseEnd_2428976 : Nat := 277162708052309745317633

theorem tailTrace_2428976 : CollatzResearch.WordTrace tailWord_2428976 prefixEnd_2428976 277162708052309745317633 := by
  unfold tailWord_2428976
  simp only [CollatzResearch.WordTrace]
  refine ⟨44296016424121131459561391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59061355232161508612748521 44296016424121131459561391)
  ·
    refine ⟨66444024636181697189342087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44296016424121131459561391 66444024636181697189342087)
    ·
      refine ⟨99666036954272545784013131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66444024636181697189342087 99666036954272545784013131)
      ·
        refine ⟨149499055431408818676019697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99666036954272545784013131 149499055431408818676019697)
        ·
          refine ⟨112124291573556614007014773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149499055431408818676019697 112124291573556614007014773)
          ·
            refine ⟨10511652335020932563157635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 112124291573556614007014773 10511652335020932563157635)
            ·
              refine ⟨15767478502531398844736453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10511652335020932563157635 15767478502531398844736453)
              ·
                refine ⟨2956402219224637283388085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15767478502531398844736453 2956402219224637283388085)
                ·
                  refine ⟨277162708052309745317633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2956402219224637283388085 277162708052309745317633)
                  ·
                    rfl

theorem cell22_2428976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 5].length) (baseStart_2428976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2428976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2428976 prefixEnd_2428976 := by exact prefixLift 2428976
  have htrace : WordTrace (prefixWord ++ tailWord_2428976) baseStart_2428976 baseEnd_2428976 := by
    simpa [prefixWord, tailWord_2428976, baseEnd_2428976] using wordTrace_append hprefix tailTrace_2428976
  have hstable : (prefixWord ++ tailWord_2428976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428976).length < 2 ^ (prefixWord ++ tailWord_2428976).sum := by decide
  have hdescent : baseEnd_2428976 < baseStart_2428976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428993 : List Nat := [1, 2, 5, 1, 2, 1, 2, 3, 5]
def baseStart_2428993 : Nat := 118140960795 + 2428993 * 2 ^ 59
def prefixEnd_2428993 : Nat := 4983230072969 + 3 ^ 40 * 2428993 * 2
def baseEnd_2428993 : Nat := 277164647868115619425949

theorem tailTrace_2428993 : CollatzResearch.WordTrace tailWord_2428993 prefixEnd_2428993 277164647868115619425949 := by
  unfold tailWord_2428993
  simp only [CollatzResearch.WordTrace]
  refine ⟨88592652889180674822491633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59061768592787116548327755 88592652889180674822491633)
  ·
    refine ⟨66444489666885506116868725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88592652889180674822491633 66444489666885506116868725)
    ·
      refine ⟨6229170906270516198456443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66444489666885506116868725 6229170906270516198456443)
      ·
        refine ⟨9343756359405774297684665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6229170906270516198456443 9343756359405774297684665)
        ·
          refine ⟨7007817269554330723263499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9343756359405774297684665 7007817269554330723263499)
          ·
            refine ⟨10511725904331496084895249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7007817269554330723263499 10511725904331496084895249)
            ·
              refine ⟨7883794428248622063671437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10511725904331496084895249 7883794428248622063671437)
              ·
                refine ⟨2956422910593233273876789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7883794428248622063671437 2956422910593233273876789)
                ·
                  refine ⟨277164647868115619425949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2956422910593233273876789 277164647868115619425949)
                  ·
                    rfl

theorem cell22_2428993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 5].length) (baseStart_2428993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2428993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2428993 prefixEnd_2428993 := by exact prefixLift 2428993
  have htrace : WordTrace (prefixWord ++ tailWord_2428993) baseStart_2428993 baseEnd_2428993 := by
    simpa [prefixWord, tailWord_2428993, baseEnd_2428993] using wordTrace_append hprefix tailTrace_2428993
  have hstable : (prefixWord ++ tailWord_2428993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428993).length < 2 ^ (prefixWord ++ tailWord_2428993).sum := by decide
  have hdescent : baseEnd_2428993 < baseStart_2428993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429014 : List Nat := [5, 2, 2, 1, 1, 1, 1, 5, 1, 3]
def baseStart_2429014 : Nat := 118140960795 + 2429014 * 2 ^ 59
def prefixEnd_2429014 : Nat := 4983230072969 + 3 ^ 40 * 2429014 * 2
def baseEnd_2429014 : Nat := 831501132333509803502783

theorem tailTrace_2429014 : CollatzResearch.WordTrace tailWord_2429014 prefixEnd_2429014 831501132333509803502783 := by
  unfold tailWord_2429014
  simp only [CollatzResearch.WordTrace]
  refine ⟨5537088676381537213062881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59062279214736396939337397 5537088676381537213062881)
  ·
    refine ⟨4152816507286152909797161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5537088676381537213062881 4152816507286152909797161)
    ·
      refine ⟨3114612380464614682347871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4152816507286152909797161 3114612380464614682347871)
      ·
        refine ⟨4671918570696922023521807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3114612380464614682347871 4671918570696922023521807)
        ·
          refine ⟨7007877856045383035282711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4671918570696922023521807 7007877856045383035282711)
          ·
            refine ⟨10511816784068074552924067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7007877856045383035282711 10511816784068074552924067)
            ·
              refine ⟨15767725176102111829386101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10511816784068074552924067 15767725176102111829386101)
              ·
                refine ⟨1478224235259572984004947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15767725176102111829386101 1478224235259572984004947)
                ·
                  refine ⟨2217336352889359476007421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1478224235259572984004947 2217336352889359476007421)
                  ·
                    refine ⟨831501132333509803502783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2217336352889359476007421 831501132333509803502783)
                    ·
                      rfl

theorem cell22_2429014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_2429014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429014 prefixEnd_2429014 := by exact prefixLift 2429014
  have htrace : WordTrace (prefixWord ++ tailWord_2429014) baseStart_2429014 baseEnd_2429014 := by
    simpa [prefixWord, tailWord_2429014, baseEnd_2429014] using wordTrace_append hprefix tailTrace_2429014
  have hstable : (prefixWord ++ tailWord_2429014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429014).length < 2 ^ (prefixWord ++ tailWord_2429014).sum := by decide
  have hdescent : baseEnd_2429014 < baseStart_2429014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429038 : List Nat := [4, 1, 2, 2, 1, 1, 4, 1, 6]
def baseStart_2429038 : Nat := 118140960795 + 2429038 * 2 ^ 59
def prefixEnd_2429038 : Nat := 4983230072969 + 3 ^ 40 * 2429038 * 2
def baseEnd_2429038 : Nat := 277169782674660580300903

theorem tailTrace_2429038 : CollatzResearch.WordTrace tailWord_2429038 prefixEnd_2429038 277169782674660580300903 := by
  unfold tailWord_2429038
  simp only [CollatzResearch.WordTrace]
  refine ⟨11074286771752205938484971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59062862782678431671919845 11074286771752205938484971)
  ·
    refine ⟨16611430157628308907727457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11074286771752205938484971 16611430157628308907727457)
    ·
      refine ⟨12458572618221231680795593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16611430157628308907727457 12458572618221231680795593)
      ·
        refine ⟨9343929463665923760596695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12458572618221231680795593 9343929463665923760596695)
        ·
          refine ⟨14015894195498885640895043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9343929463665923760596695 14015894195498885640895043)
          ·
            refine ⟨21023841293248328461342565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14015894195498885640895043 21023841293248328461342565)
            ·
              refine ⟨3941970242484061586501731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21023841293248328461342565 3941970242484061586501731)
              ·
                refine ⟨5912955363726092379752597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3941970242484061586501731 5912955363726092379752597)
                ·
                  refine ⟨277169782674660580300903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5912955363726092379752597 277169782674660580300903)
                  ·
                    rfl

theorem cell22_2429038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_2429038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429038 prefixEnd_2429038 := by exact prefixLift 2429038
  have htrace : WordTrace (prefixWord ++ tailWord_2429038) baseStart_2429038 baseEnd_2429038 := by
    simpa [prefixWord, tailWord_2429038, baseEnd_2429038] using wordTrace_append hprefix tailTrace_2429038
  have hstable : (prefixWord ++ tailWord_2429038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429038).length < 2 ^ (prefixWord ++ tailWord_2429038).sum := by decide
  have hdescent : baseEnd_2429038 < baseStart_2429038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429053 : List Nat := [1, 4, 1, 1, 3, 2, 3, 1, 1, 5]
def baseStart_2429053 : Nat := 118140960795 + 2429053 * 2 ^ 59
def prefixEnd_2429053 : Nat := 4983230072969 + 3 ^ 40 * 2429053 * 2
def baseEnd_2429053 : Nat := 831514482830526701777663

theorem tailTrace_2429053 : CollatzResearch.WordTrace tailWord_2429053 prefixEnd_2429053 831514482830526701777663 := by
  unfold tailWord_2429053
  simp only [CollatzResearch.WordTrace]
  refine ⟨88594841268963305069675813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59063227512642203379783875 88594841268963305069675813)
  ·
    refine ⟨16611532737930619700564215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88594841268963305069675813 16611532737930619700564215)
    ·
      refine ⟨24917299106895929550846323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16611532737930619700564215 24917299106895929550846323)
      ·
        refine ⟨37375948660343894326269485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24917299106895929550846323 37375948660343894326269485)
        ·
          refine ⟨14015980747628960372351057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37375948660343894326269485 14015980747628960372351057)
          ·
            refine ⟨10511985560721720279263293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14015980747628960372351057 10511985560721720279263293)
            ·
              refine ⟨3941994585270645104723735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10511985560721720279263293 3941994585270645104723735)
              ·
                refine ⟨5912991877905967657085603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3941994585270645104723735 5912991877905967657085603)
                ·
                  refine ⟨8869487816858951485628405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5912991877905967657085603 8869487816858951485628405)
                  ·
                    refine ⟨831514482830526701777663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8869487816858951485628405 831514482830526701777663)
                    ·
                      rfl

theorem cell22_2429053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_2429053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429053 prefixEnd_2429053 := by exact prefixLift 2429053
  have htrace : WordTrace (prefixWord ++ tailWord_2429053) baseStart_2429053 baseEnd_2429053 := by
    simpa [prefixWord, tailWord_2429053, baseEnd_2429053] using wordTrace_append hprefix tailTrace_2429053
  have hstable : (prefixWord ++ tailWord_2429053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429053).length < 2 ^ (prefixWord ++ tailWord_2429053).sum := by decide
  have hdescent : baseEnd_2429053 < baseStart_2429053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429108 : List Nat := [2, 5, 3, 1, 2, 1, 1, 2, 1, 4]
def baseStart_2429108 : Nat := 118140960795 + 2429108 * 2 ^ 59
def prefixEnd_2429108 : Nat := 4983230072969 + 3 ^ 40 * 2429108 * 2
def baseEnd_2429108 : Nat := 831533310454524891652495

theorem tailTrace_2429108 : CollatzResearch.WordTrace tailWord_2429108 prefixEnd_2429108 831533310454524891652495 := by
  unfold tailWord_2429108
  simp only [CollatzResearch.WordTrace]
  refine ⟨44298423641882024731463989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59064564855842699641951985 44298423641882024731463989)
  ·
    refine ⟨4152977216426439818574749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44298423641882024731463989 4152977216426439818574749)
    ·
      refine ⟨1557366456159914931965531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4152977216426439818574749 1557366456159914931965531)
      ·
        refine ⟨2336049684239872397948297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1557366456159914931965531 2336049684239872397948297)
        ·
          refine ⟨1752037263179904298461223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2336049684239872397948297 1752037263179904298461223)
          ·
            refine ⟨2628055894769856447691835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1752037263179904298461223 2628055894769856447691835)
            ·
              refine ⟨3942083842154784671537753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2628055894769856447691835 3942083842154784671537753)
              ·
                refine ⟨2956562881616088503653315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3942083842154784671537753 2956562881616088503653315)
                ·
                  refine ⟨4434844322424132755479973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2956562881616088503653315 4434844322424132755479973)
                  ·
                    refine ⟨831533310454524891652495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4434844322424132755479973 831533310454524891652495)
                    ·
                      rfl

theorem cell22_2429108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_2429108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429108 prefixEnd_2429108 := by exact prefixLift 2429108
  have htrace : WordTrace (prefixWord ++ tailWord_2429108) baseStart_2429108 baseEnd_2429108 := by
    simpa [prefixWord, tailWord_2429108, baseEnd_2429108] using wordTrace_append hprefix tailTrace_2429108
  have hstable : (prefixWord ++ tailWord_2429108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429108).length < 2 ^ (prefixWord ++ tailWord_2429108).sum := by decide
  have hdescent : baseEnd_2429108 < baseStart_2429108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429149 : List Nat := [1, 4, 3, 2, 1, 2, 1, 4, 1, 3]
def baseStart_2429149 : Nat := 118140960795 + 2429149 * 2 ^ 59
def prefixEnd_2429149 : Nat := 4983230072969 + 3 ^ 40 * 2429149 * 2
def baseEnd_2429149 : Nat := 831547345592414451377369

theorem tailTrace_2429149 : CollatzResearch.WordTrace tailWord_2429149 prefixEnd_2429149 831547345592414451377369 := by
  unfold tailWord_2429149
  simp only [CollatzResearch.WordTrace]
  refine ⟨88598342676615513465170501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59065561784410342310113667 88598342676615513465170501)
  ·
    refine ⟨16612189251865408774719469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88598342676615513465170501 16612189251865408774719469)
    ·
      refine ⟨6229570969449528290519801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16612189251865408774719469 6229570969449528290519801)
      ·
        refine ⟨4672178227087146217889851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6229570969449528290519801 4672178227087146217889851)
        ·
          refine ⟨7008267340630719326834777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4672178227087146217889851 7008267340630719326834777)
          ·
            refine ⟨5256200505473039495126083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7008267340630719326834777 5256200505473039495126083)
            ·
              refine ⟨7884300758209559242689125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5256200505473039495126083 7884300758209559242689125)
              ·
                refine ⟨1478306392164292358004211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7884300758209559242689125 1478306392164292358004211)
                ·
                  refine ⟨2217459588246438537006317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1478306392164292358004211 2217459588246438537006317)
                  ·
                    refine ⟨831547345592414451377369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2217459588246438537006317 831547345592414451377369)
                    ·
                      rfl

theorem cell22_2429149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_2429149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429149 prefixEnd_2429149 := by exact prefixLift 2429149
  have htrace : WordTrace (prefixWord ++ tailWord_2429149) baseStart_2429149 baseEnd_2429149 := by
    simpa [prefixWord, tailWord_2429149, baseEnd_2429149] using wordTrace_append hprefix tailTrace_2429149
  have hstable : (prefixWord ++ tailWord_2429149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429149).length < 2 ^ (prefixWord ++ tailWord_2429149).sum := by decide
  have hdescent : baseEnd_2429149 < baseStart_2429149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429192 : List Nat := [2, 1, 3, 2, 3, 1, 4, 1, 1, 4]
def baseStart_2429192 : Nat := 118140960795 + 2429192 * 2 ^ 59
def prefixEnd_2429192 : Nat := 4983230072969 + 3 ^ 40 * 2429192 * 2
def baseEnd_2429192 : Nat := 831562065371176672552237

theorem tailTrace_2429192 : CollatzResearch.WordTrace tailWord_2429192 prefixEnd_2429192 831562065371176672552237 := by
  unfold tailWord_2429192
  simp only [CollatzResearch.WordTrace]
  refine ⟨44299955507729865904492915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59066607343639821205990553 44299955507729865904492915)
  ·
    refine ⟨66449933261594798856739373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44299955507729865904492915 66449933261594798856739373)
    ·
      refine ⟨24918724973098049571277265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66449933261594798856739373 24918724973098049571277265)
      ·
        refine ⟨18689043729823537178457949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24918724973098049571277265 18689043729823537178457949)
        ·
          refine ⟨7008391398683826441921731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18689043729823537178457949 7008391398683826441921731)
          ·
            refine ⟨10512587098025739662882597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7008391398683826441921731 10512587098025739662882597)
            ·
              refine ⟨1971110080879826186790487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10512587098025739662882597 1971110080879826186790487)
              ·
                refine ⟨2956665121319739280185731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1971110080879826186790487 2956665121319739280185731)
                ·
                  refine ⟨4434997681979608920278597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2956665121319739280185731 4434997681979608920278597)
                  ·
                    refine ⟨831562065371176672552237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4434997681979608920278597 831562065371176672552237)
                    ·
                      rfl

theorem cell22_2429192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_2429192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429192 prefixEnd_2429192 := by exact prefixLift 2429192
  have htrace : WordTrace (prefixWord ++ tailWord_2429192) baseStart_2429192 baseEnd_2429192 := by
    simpa [prefixWord, tailWord_2429192, baseEnd_2429192] using wordTrace_append hprefix tailTrace_2429192
  have hstable : (prefixWord ++ tailWord_2429192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429192).length < 2 ^ (prefixWord ++ tailWord_2429192).sum := by decide
  have hdescent : baseEnd_2429192 < baseStart_2429192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429203 : List Nat := [1, 1, 1, 2, 1, 3, 1, 6, 2, 4]
def baseStart_2429203 : Nat := 118140960795 + 2429203 * 2 ^ 59
def prefixEnd_2429203 : Nat := 4983230072969 + 3 ^ 40 * 2429203 * 2
def baseEnd_2429203 : Nat := 831565830895976310527203

theorem tailTrace_2429203 : CollatzResearch.WordTrace tailWord_2429203 prefixEnd_2429203 831565830895976310527203 := by
  unfold tailWord_2429203
  simp only [CollatzResearch.WordTrace]
  refine ⟨88600312218419880687636263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59066874812279920458424175 88600312218419880687636263)
  ·
    refine ⟨132900468327629821031454395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88600312218419880687636263 132900468327629821031454395)
    ·
      refine ⟨199350702491444731547181593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132900468327629821031454395 199350702491444731547181593)
      ·
        refine ⟨149513026868583548660386195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199350702491444731547181593 149513026868583548660386195)
        ·
          refine ⟨224269540302875322990579293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149513026868583548660386195 224269540302875322990579293)
          ·
            refine ⟨84101077613578246121467235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 224269540302875322990579293 84101077613578246121467235)
            ·
              refine ⟨126151616420367369182200853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84101077613578246121467235 126151616420367369182200853)
              ·
                refine ⟨5913357019704720430415665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 126151616420367369182200853 5913357019704720430415665)
                ·
                  refine ⟨4435017764778540322811749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5913357019704720430415665 4435017764778540322811749)
                  ·
                    refine ⟨831565830895976310527203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4435017764778540322811749 831565830895976310527203)
                    ·
                      rfl

theorem cell22_2429203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 4].length) (baseStart_2429203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429203 prefixEnd_2429203 := by exact prefixLift 2429203
  have htrace : WordTrace (prefixWord ++ tailWord_2429203) baseStart_2429203 baseEnd_2429203 := by
    simpa [prefixWord, tailWord_2429203, baseEnd_2429203] using wordTrace_append hprefix tailTrace_2429203
  have hstable : (prefixWord ++ tailWord_2429203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429203).length < 2 ^ (prefixWord ++ tailWord_2429203).sum := by decide
  have hdescent : baseEnd_2429203 < baseStart_2429203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429252 : List Nat := [2, 3, 4, 1, 2, 2, 8]
def baseStart_2429252 : Nat := 118140960795 + 2429252 * 2 ^ 59
def prefixEnd_2429252 : Nat := 4983230072969 + 3 ^ 40 * 2429252 * 2
def baseEnd_2429252 : Nat := 30799355725828019113039

theorem tailTrace_2429252 : CollatzResearch.WordTrace tailWord_2429252 prefixEnd_2429252 30799355725828019113039 := by
  unfold tailWord_2429252
  simp only [CollatzResearch.WordTrace]
  refine ⟨44301049697621181028085005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59068066263494908037446673 44301049697621181028085005)
  ·
    refine ⟨16612893636607942885531877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44301049697621181028085005 16612893636607942885531877)
    ·
      refine ⟨3114917556863989291037227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16612893636607942885531877 3114917556863989291037227)
      ·
        refine ⟨4672376335295983936555841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3114917556863989291037227 4672376335295983936555841)
        ·
          refine ⟨3504282251471987952416881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4672376335295983936555841 3504282251471987952416881)
          ·
            refine ⟨2628211688603990964312661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3504282251471987952416881 2628211688603990964312661)
            ·
              refine ⟨30799355725828019113039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2628211688603990964312661 30799355725828019113039)
              ·
                rfl

theorem cell22_2429252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 8].length) (baseStart_2429252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429252 prefixEnd_2429252 := by exact prefixLift 2429252
  have htrace : WordTrace (prefixWord ++ tailWord_2429252) baseStart_2429252 baseEnd_2429252 := by
    simpa [prefixWord, tailWord_2429252, baseEnd_2429252] using wordTrace_append hprefix tailTrace_2429252
  have hstable : (prefixWord ++ tailWord_2429252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429252).length < 2 ^ (prefixWord ++ tailWord_2429252).sum := by decide
  have hdescent : baseEnd_2429252 < baseStart_2429252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429308 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 10]
def baseStart_2429308 : Nat := 118140960795 + 2429308 * 2 ^ 59
def prefixEnd_2429308 : Nat := 4983230072969 + 3 ^ 40 * 2429308 * 2
def baseEnd_2429308 : Nat := 277200591513930345550627

theorem tailTrace_2429308 : CollatzResearch.WordTrace tailWord_2429308 prefixEnd_2429308 277200591513930345550627 := by
  unfold tailWord_2429308
  simp only [CollatzResearch.WordTrace]
  refine ⟨44302070941519741810104289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59069427922026322413472385 44302070941519741810104289)
  ·
    refine ⟨33226553206139806357578217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44302070941519741810104289 33226553206139806357578217)
    ·
      refine ⟨24919914904604854768183663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33226553206139806357578217 24919914904604854768183663)
      ·
        refine ⟨37379872356907282152275495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24919914904604854768183663 37379872356907282152275495)
        ·
          refine ⟨56069808535360923228413243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37379872356907282152275495 56069808535360923228413243)
          ·
            refine ⟨84104712803041384842619865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56069808535360923228413243 84104712803041384842619865)
            ·
              refine ⟨63078534602281038631964899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84104712803041384842619865 63078534602281038631964899)
              ·
                refine ⟨94617801903421557947947349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63078534602281038631964899 94617801903421557947947349)
                ·
                  refine ⟨277200591513930345550627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 94617801903421557947947349 277200591513930345550627)
                  ·
                    rfl

theorem cell22_2429308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 10].length) (baseStart_2429308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429308 prefixEnd_2429308 := by exact prefixLift 2429308
  have htrace : WordTrace (prefixWord ++ tailWord_2429308) baseStart_2429308 baseEnd_2429308 := by
    simpa [prefixWord, tailWord_2429308, baseEnd_2429308] using wordTrace_append hprefix tailTrace_2429308
  have hstable : (prefixWord ++ tailWord_2429308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429308).length < 2 ^ (prefixWord ++ tailWord_2429308).sum := by decide
  have hdescent : baseEnd_2429308 < baseStart_2429308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429342 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 8]
def baseStart_2429342 : Nat := 118140960795 + 2429342 * 2 ^ 59
def prefixEnd_2429342 : Nat := 4983230072969 + 3 ^ 40 * 2429342 * 2
def baseEnd_2429342 : Nat := 277204471145542093767259

theorem tailTrace_2429342 : CollatzResearch.WordTrace tailWord_2429342 prefixEnd_2429342 277204471145542093767259 := by
  unfold tailWord_2429342
  simp only [CollatzResearch.WordTrace]
  refine ⟨11075672745614538428368285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59070254643277538284630853 11075672745614538428368285)
  ·
    refine ⟨4153377279605451910638107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11075672745614538428368285 4153377279605451910638107)
    ·
      refine ⟨6230065919408177865957161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4153377279605451910638107 6230065919408177865957161)
      ·
        refine ⟨4672549439556133399467871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6230065919408177865957161 4672549439556133399467871)
        ·
          refine ⟨7008824159334200099201807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4672549439556133399467871 7008824159334200099201807)
          ·
            refine ⟨10513236239001300148802711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7008824159334200099201807 10513236239001300148802711)
            ·
              refine ⟨15769854358501950223204067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10513236239001300148802711 15769854358501950223204067)
              ·
                refine ⟨23654781537752925334806101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15769854358501950223204067 23654781537752925334806101)
                ·
                  refine ⟨277204471145542093767259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23654781537752925334806101 277204471145542093767259)
                  ·
                    rfl

theorem cell22_2429342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_2429342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429342 prefixEnd_2429342 := by exact prefixLift 2429342
  have htrace : WordTrace (prefixWord ++ tailWord_2429342) baseStart_2429342 baseEnd_2429342 := by
    simpa [prefixWord, tailWord_2429342, baseEnd_2429342] using wordTrace_append hprefix tailTrace_2429342
  have hstable : (prefixWord ++ tailWord_2429342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429342).length < 2 ^ (prefixWord ++ tailWord_2429342).sum := by decide
  have hdescent : baseEnd_2429342 < baseStart_2429342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429353 : List Nat := [1, 2, 1, 1, 1, 1, 3, 12]
def baseStart_2429353 : Nat := 118140960795 + 2429353 * 2 ^ 59
def prefixEnd_2429353 : Nat := 4983230072969 + 3 ^ 40 * 2429353 * 2
def baseEnd_2429353 : Nat := 92401908773491768808527

theorem tailTrace_2429353 : CollatzResearch.WordTrace tailWord_2429353 prefixEnd_2429353 92401908773491768808527 := by
  unfold tailWord_2429353
  simp only [CollatzResearch.WordTrace]
  refine ⟨88605783167876456305596713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59070522111917637537064475 88605783167876456305596713)
  ·
    refine ⟨66454337375907342229197535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88605783167876456305596713 66454337375907342229197535)
    ·
      refine ⟨99681506063861013343796303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66454337375907342229197535 99681506063861013343796303)
      ·
        refine ⟨149522259095791520015694455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99681506063861013343796303 149522259095791520015694455)
        ·
          refine ⟨224283388643687280023541683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149522259095791520015694455 224283388643687280023541683)
          ·
            refine ⟨336425082965530920035312525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224283388643687280023541683 336425082965530920035312525)
            ·
              refine ⟨126159406112074095013242197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 336425082965530920035312525 126159406112074095013242197)
              ·
                refine ⟨92401908773491768808527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 126159406112074095013242197 92401908773491768808527)
                ·
                  rfl

theorem cell22_2429353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 12].length) (baseStart_2429353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429353 prefixEnd_2429353 := by exact prefixLift 2429353
  have htrace : WordTrace (prefixWord ++ tailWord_2429353) baseStart_2429353 baseEnd_2429353 := by
    simpa [prefixWord, tailWord_2429353, baseEnd_2429353] using wordTrace_append hprefix tailTrace_2429353
  have hstable : (prefixWord ++ tailWord_2429353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429353).length < 2 ^ (prefixWord ++ tailWord_2429353).sum := by decide
  have hdescent : baseEnd_2429353 < baseStart_2429353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429374 : List Nat := [4, 2, 1, 1, 1, 1, 5, 2, 2, 3]
def baseStart_2429374 : Nat := 118140960795 + 2429374 * 2 ^ 59
def prefixEnd_2429374 : Nat := 4983230072969 + 3 ^ 40 * 2429374 * 2
def baseEnd_2429374 : Nat := 831624367690588864501679

theorem tailTrace_2429374 : CollatzResearch.WordTrace tailWord_2429374 prefixEnd_2429374 831624367690588864501679 := by
  unfold tailWord_2429374
  simp only [CollatzResearch.WordTrace]
  refine ⟨11075818637600047111513897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59071032733866917928074117 11075818637600047111513897)
  ·
    refine ⟨8306863978200035333635423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11075818637600047111513897 8306863978200035333635423)
    ·
      refine ⟨12460295967300053000453135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8306863978200035333635423 12460295967300053000453135)
      ·
        refine ⟨18690443950950079500679703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12460295967300053000453135 18690443950950079500679703)
        ·
          refine ⟨28035665926425119251019555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18690443950950079500679703 28035665926425119251019555)
          ·
            refine ⟨42053498889637678876529333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28035665926425119251019555 42053498889637678876529333)
            ·
              refine ⟨3942515520903532394674625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42053498889637678876529333 3942515520903532394674625)
              ·
                refine ⟨2956886640677649296005969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3942515520903532394674625 2956886640677649296005969)
                ·
                  refine ⟨2217664980508236972004477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2956886640677649296005969 2217664980508236972004477)
                  ·
                    refine ⟨831624367690588864501679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2217664980508236972004477 831624367690588864501679)
                    ·
                      rfl

theorem cell22_2429374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_2429374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429374 prefixEnd_2429374 := by exact prefixLift 2429374
  have htrace : WordTrace (prefixWord ++ tailWord_2429374) baseStart_2429374 baseEnd_2429374 := by
    simpa [prefixWord, tailWord_2429374, baseEnd_2429374] using wordTrace_append hprefix tailTrace_2429374
  have hstable : (prefixWord ++ tailWord_2429374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429374).length < 2 ^ (prefixWord ++ tailWord_2429374).sum := by decide
  have hdescent : baseEnd_2429374 < baseStart_2429374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429402 : List Nat := [3, 1, 1, 2, 3, 1, 1, 4, 3, 3]
def baseStart_2429402 : Nat := 118140960795 + 2429402 * 2 ^ 59
def prefixEnd_2429402 : Nat := 4983230072969 + 3 ^ 40 * 2429402 * 2
def baseEnd_2429402 : Nat := 831633952662806124801593

theorem tailTrace_2429402 : CollatzResearch.WordTrace tailWord_2429402 prefixEnd_2429402 831633952662806124801593 := by
  unfold tailWord_2429402
  simp only [CollatzResearch.WordTrace]
  refine ⟨22151892586174734418532615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59071713563132625116086973 22151892586174734418532615)
  ·
    refine ⟨33227838879262101627798923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22151892586174734418532615 33227838879262101627798923)
    ·
      refine ⟨49841758318893152441698385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33227838879262101627798923 49841758318893152441698385)
      ·
        refine ⟨37381318739169864331273789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49841758318893152441698385 37381318739169864331273789)
        ·
          refine ⟨14017994527188699124227671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37381318739169864331273789 14017994527188699124227671)
          ·
            refine ⟨21026991790783048686341507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14017994527188699124227671 21026991790783048686341507)
            ·
              refine ⟨31540487686174573029512261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21026991790783048686341507 31540487686174573029512261)
              ·
                refine ⟨5913841441157732443033549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31540487686174573029512261 5913841441157732443033549)
                ·
                  refine ⟨2217690540434149666137581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5913841441157732443033549 2217690540434149666137581)
                  ·
                    refine ⟨831633952662806124801593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2217690540434149666137581 831633952662806124801593)
                    ·
                      rfl

theorem cell22_2429402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 3, 3].length) (baseStart_2429402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429402 prefixEnd_2429402 := by exact prefixLift 2429402
  have htrace : WordTrace (prefixWord ++ tailWord_2429402) baseStart_2429402 baseEnd_2429402 := by
    simpa [prefixWord, tailWord_2429402, baseEnd_2429402] using wordTrace_append hprefix tailTrace_2429402
  have hstable : (prefixWord ++ tailWord_2429402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429402).length < 2 ^ (prefixWord ++ tailWord_2429402).sum := by decide
  have hdescent : baseEnd_2429402 < baseStart_2429402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429410 : List Nat := [3, 3, 3, 2, 2, 1, 1, 3, 4]
def baseStart_2429410 : Nat := 118140960795 + 2429410 * 2 ^ 59
def prefixEnd_2429410 : Nat := 4983230072969 + 3 ^ 40 * 2429410 * 2
def baseEnd_2429410 : Nat := 277212230408765590200523

theorem tailTrace_2429410 : CollatzResearch.WordTrace tailWord_2429410 prefixEnd_2429410 277212230408765590200523 := by
  unfold tailWord_2429410
  simp only [CollatzResearch.WordTrace]
  refine ⟨22151965532167488760105421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59071908085779970026947789 22151965532167488760105421)
  ·
    refine ⟨8306987074562808285039533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22151965532167488760105421 8306987074562808285039533)
    ·
      refine ⟨3115120152961053106889825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8306987074562808285039533 3115120152961053106889825)
      ·
        refine ⟨2336340114720789830167369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3115120152961053106889825 2336340114720789830167369)
        ·
          refine ⟨1752255086040592372625527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2336340114720789830167369 1752255086040592372625527)
          ·
            refine ⟨2628382629060888558938291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1752255086040592372625527 2628382629060888558938291)
            ·
              refine ⟨3942573943591332838407437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2628382629060888558938291 3942573943591332838407437)
              ·
                refine ⟨1478465228846749814402789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3942573943591332838407437 1478465228846749814402789)
                ·
                  refine ⟨277212230408765590200523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1478465228846749814402789 277212230408765590200523)
                  ·
                    rfl

theorem cell22_2429410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_2429410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429410 prefixEnd_2429410 := by exact prefixLift 2429410
  have htrace : WordTrace (prefixWord ++ tailWord_2429410) baseStart_2429410 baseEnd_2429410 := by
    simpa [prefixWord, tailWord_2429410, baseEnd_2429410] using wordTrace_append hprefix tailTrace_2429410
  have hstable : (prefixWord ++ tailWord_2429410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429410).length < 2 ^ (prefixWord ++ tailWord_2429410).sum := by decide
  have hdescent : baseEnd_2429410 < baseStart_2429410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429415 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 9]
def baseStart_2429415 : Nat := 118140960795 + 2429415 * 2 ^ 59
def prefixEnd_2429415 : Nat := 4983230072969 + 3 ^ 40 * 2429415 * 2
def baseEnd_2429415 : Nat := 277212800942826141408851

theorem tailTrace_2429415 : CollatzResearch.WordTrace tailWord_2429415 prefixEnd_2429415 277212800942826141408851 := by
  unfold tailWord_2429415
  simp only [CollatzResearch.WordTrace]
  refine ⟨88608044493651840894353699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59072029662434560596235799 88608044493651840894353699)
  ·
    refine ⟨132912066740477761341530549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88608044493651840894353699 132912066740477761341530549)
    ·
      refine ⟨12460506256919790125768489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 132912066740477761341530549 12460506256919790125768489)
      ·
        refine ⟨9345379692689842594326367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12460506256919790125768489 9345379692689842594326367)
        ·
          refine ⟨14018069539034763891489551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9345379692689842594326367 14018069539034763891489551)
          ·
            refine ⟨21027104308552145837234327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14018069539034763891489551 21027104308552145837234327)
            ·
              refine ⟨31540656462828218755851491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21027104308552145837234327 31540656462828218755851491)
              ·
                refine ⟨47310984694242328133777237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31540656462828218755851491 47310984694242328133777237)
                ·
                  refine ⟨277212800942826141408851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47310984694242328133777237 277212800942826141408851)
                  ·
                    rfl

theorem cell22_2429415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 9].length) (baseStart_2429415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429415 prefixEnd_2429415 := by exact prefixLift 2429415
  have htrace : WordTrace (prefixWord ++ tailWord_2429415) baseStart_2429415 baseEnd_2429415 := by
    simpa [prefixWord, tailWord_2429415, baseEnd_2429415] using wordTrace_append hprefix tailTrace_2429415
  have hstable : (prefixWord ++ tailWord_2429415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429415).length < 2 ^ (prefixWord ++ tailWord_2429415).sum := by decide
  have hdescent : baseEnd_2429415 < baseStart_2429415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429509 : List Nat := [1, 3, 1, 1, 1, 5, 2, 3, 2, 3]
def baseStart_2429509 : Nat := 118140960795 + 2429509 * 2 ^ 59
def prefixEnd_2429509 : Nat := 4983230072969 + 3 ^ 40 * 2429509 * 2
def baseEnd_2429509 : Nat := 831670580949493512376265

theorem tailTrace_2429509 : CollatzResearch.WordTrace tailWord_2429509 prefixEnd_2429509 831670580949493512376265 := by
  unfold tailWord_2429509
  simp only [CollatzResearch.WordTrace]
  refine ⟨88611472955311294948275581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59074315303540863298850387 88611472955311294948275581)
  ·
    refine ⟨33229302358241735605603343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88611472955311294948275581 33229302358241735605603343)
    ·
      refine ⟨49843953537362603408405015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33229302358241735605603343 49843953537362603408405015)
      ·
        refine ⟨74765930306043905112607523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49843953537362603408405015 74765930306043905112607523)
        ·
          refine ⟨112148895459065857668911285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74765930306043905112607523 112148895459065857668911285)
          ·
            refine ⟨10513958949287424156460433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 112148895459065857668911285 10513958949287424156460433)
            ·
              refine ⟨7885469211965568117345325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10513958949287424156460433 7885469211965568117345325)
              ·
                refine ⟨2957050954487088044004497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7885469211965568117345325 2957050954487088044004497)
                ·
                  refine ⟨2217788215865316033003373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2957050954487088044004497 2217788215865316033003373)
                  ·
                    refine ⟨831670580949493512376265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2217788215865316033003373 831670580949493512376265)
                    ·
                      rfl

theorem cell22_2429509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 2, 3].length) (baseStart_2429509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429509 prefixEnd_2429509 := by exact prefixLift 2429509
  have htrace : WordTrace (prefixWord ++ tailWord_2429509) baseStart_2429509 baseEnd_2429509 := by
    simpa [prefixWord, tailWord_2429509, baseEnd_2429509] using wordTrace_append hprefix tailTrace_2429509
  have hstable : (prefixWord ++ tailWord_2429509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429509).length < 2 ^ (prefixWord ++ tailWord_2429509).sum := by decide
  have hdescent : baseEnd_2429509 < baseStart_2429509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429520 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 1, 9]
def baseStart_2429520 : Nat := 118140960795 + 2429520 * 2 ^ 59
def prefixEnd_2429520 : Nat := 4983230072969 + 3 ^ 40 * 2429520 * 2
def baseEnd_2429520 : Nat := 831674346474293150351231

theorem tailTrace_2429520 : CollatzResearch.WordTrace tailWord_2429520 prefixEnd_2429520 831674346474293150351231 := by
  unfold tailWord_2429520
  simp only [CollatzResearch.WordTrace]
  refine ⟨44305937079135721913463007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59074582772180962551284009 44305937079135721913463007)
  ·
    refine ⟨66458905618703582870194511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44305937079135721913463007 66458905618703582870194511)
    ·
      refine ⟨99688358428055374305291767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66458905618703582870194511 99688358428055374305291767)
      ·
        refine ⟨149532537642083061457937651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99688358428055374305291767 149532537642083061457937651)
        ·
          refine ⟨224298806463124592186906477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149532537642083061457937651 224298806463124592186906477)
          ·
            refine ⟨84112052423671722070089929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 224298806463124592186906477 84112052423671722070089929)
            ·
              refine ⟨63084039317753791552567447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84112052423671722070089929 63084039317753791552567447)
              ·
                refine ⟨94626058976630687328851171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63084039317753791552567447 94626058976630687328851171)
                ·
                  refine ⟨141939088464946030993276757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94626058976630687328851171 141939088464946030993276757)
                  ·
                    refine ⟨831674346474293150351231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 141939088464946030993276757 831674346474293150351231)
                    ·
                      rfl

theorem cell22_2429520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 9].length) (baseStart_2429520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429520 prefixEnd_2429520 := by exact prefixLift 2429520
  have htrace : WordTrace (prefixWord ++ tailWord_2429520) baseStart_2429520 baseEnd_2429520 := by
    simpa [prefixWord, tailWord_2429520, baseEnd_2429520] using wordTrace_append hprefix tailTrace_2429520
  have hstable : (prefixWord ++ tailWord_2429520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429520).length < 2 ^ (prefixWord ++ tailWord_2429520).sum := by decide
  have hdescent : baseEnd_2429520 < baseStart_2429520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429524 : List Nat := [2, 4, 1, 1, 1, 3, 3, 1, 2, 4]
def baseStart_2429524 : Nat := 118140960795 + 2429524 * 2 ^ 59
def prefixEnd_2429524 : Nat := 4983230072969 + 3 ^ 40 * 2429524 * 2
def baseEnd_2429524 : Nat := 831675715756038473251219

theorem tailTrace_2429524 : CollatzResearch.WordTrace tailWord_2429524 prefixEnd_2429524 831675715756038473251219 := by
  unfold tailWord_2429524
  simp only [CollatzResearch.WordTrace]
  refine ⟨44306010025128476255035813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59074680033504635006714417 44306010025128476255035813)
  ·
    refine ⟨8307376879711589297819215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44306010025128476255035813 8307376879711589297819215)
    ·
      refine ⟨12461065319567383946728823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8307376879711589297819215 12461065319567383946728823)
      ·
        refine ⟨18691597979351075920093235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12461065319567383946728823 18691597979351075920093235)
        ·
          refine ⟨28037396969026613880139853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18691597979351075920093235 28037396969026613880139853)
          ·
            refine ⟨10514023863384980205052445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28037396969026613880139853 10514023863384980205052445)
            ·
              refine ⟨3942758948769367576894667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10514023863384980205052445 3942758948769367576894667)
              ·
                refine ⟨5914138423154051365342001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3942758948769367576894667 5914138423154051365342001)
                ·
                  refine ⟨4435603817365538524006501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5914138423154051365342001 4435603817365538524006501)
                  ·
                    refine ⟨831675715756038473251219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4435603817365538524006501 831675715756038473251219)
                    ·
                      rfl

theorem cell22_2429524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_2429524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429524 prefixEnd_2429524 := by exact prefixLift 2429524
  have htrace : WordTrace (prefixWord ++ tailWord_2429524) baseStart_2429524 baseEnd_2429524 := by
    simpa [prefixWord, tailWord_2429524, baseEnd_2429524] using wordTrace_append hprefix tailTrace_2429524
  have hstable : (prefixWord ++ tailWord_2429524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429524).length < 2 ^ (prefixWord ++ tailWord_2429524).sum := by decide
  have hdescent : baseEnd_2429524 < baseStart_2429524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429631 : List Nat := [1, 1, 2, 2, 2, 6, 1, 2, 1, 4]
def baseStart_2429631 : Nat := 118140960795 + 2429631 * 2 ^ 59
def prefixEnd_2429631 : Nat := 4983230072969 + 3 ^ 40 * 2429631 * 2
def baseEnd_2429631 : Nat := 831712344042725860825891

theorem tailTrace_2429631 : CollatzResearch.WordTrace tailWord_2429631 prefixEnd_2429631 831712344042725860825891 := by
  unfold tailWord_2429631
  simp only [CollatzResearch.WordTrace]
  refine ⟨88615922660869309784216747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59077281773912873189477831 88615922660869309784216747)
  ·
    refine ⟨132923883991303964676325121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88615922660869309784216747 132923883991303964676325121)
    ·
      refine ⟨99692912993477973507243841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132923883991303964676325121 99692912993477973507243841)
      ·
        refine ⟨74769684745108480130432881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99692912993477973507243841 74769684745108480130432881)
        ·
          refine ⟨56077263558831360097824661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74769684745108480130432881 56077263558831360097824661)
          ·
            refine ⟨2628621729320220004585531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 56077263558831360097824661 2628621729320220004585531)
            ·
              refine ⟨3942932593980330006878297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2628621729320220004585531 3942932593980330006878297)
              ·
                refine ⟨2957199445485247505158723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3942932593980330006878297 2957199445485247505158723)
                ·
                  refine ⟨4435799168227871257738085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2957199445485247505158723 4435799168227871257738085)
                  ·
                    refine ⟨831712344042725860825891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4435799168227871257738085 831712344042725860825891)
                    ·
                      rfl

theorem cell22_2429631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 4].length) (baseStart_2429631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429631 prefixEnd_2429631 := by exact prefixLift 2429631
  have htrace : WordTrace (prefixWord ++ tailWord_2429631) baseStart_2429631 baseEnd_2429631 := by
    simpa [prefixWord, tailWord_2429631, baseEnd_2429631] using wordTrace_append hprefix tailTrace_2429631
  have hstable : (prefixWord ++ tailWord_2429631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429631).length < 2 ^ (prefixWord ++ tailWord_2429631).sum := by decide
  have hdescent : baseEnd_2429631 < baseStart_2429631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429644 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 3, 5]
def baseStart_2429644 : Nat := 118140960795 + 2429644 * 2 ^ 59
def prefixEnd_2429644 : Nat := 4983230072969 + 3 ^ 40 * 2429644 * 2
def baseEnd_2429644 : Nat := 831716794208398160250851

theorem tailTrace_2429644 : CollatzResearch.WordTrace tailWord_2429644 prefixEnd_2429644 831716794208398160250851 := by
  unfold tailWord_2429644
  simp only [CollatzResearch.WordTrace]
  refine ⟨44308198404911106502219993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59077597873214808669626657 44308198404911106502219993)
  ·
    refine ⟨33231148803683329876664995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44308198404911106502219993 33231148803683329876664995)
    ·
      refine ⟨49846723205524994814997493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33231148803683329876664995 49846723205524994814997493)
      ·
        refine ⟨4673130300517968263906015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49846723205524994814997493 4673130300517968263906015)
        ·
          refine ⟨7009695450776952395859023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4673130300517968263906015 7009695450776952395859023)
          ·
            refine ⟨10514543176165428593788535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7009695450776952395859023 10514543176165428593788535)
            ·
              refine ⟨15771814764248142890682803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10514543176165428593788535 15771814764248142890682803)
              ·
                refine ⟨23657722146372214336024205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15771814764248142890682803 23657722146372214336024205)
                ·
                  refine ⟨8871645804889580376009077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23657722146372214336024205 8871645804889580376009077)
                  ·
                    refine ⟨831716794208398160250851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8871645804889580376009077 831716794208398160250851)
                    ·
                      rfl

theorem cell22_2429644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_2429644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429644 prefixEnd_2429644 := by exact prefixLift 2429644
  have htrace : WordTrace (prefixWord ++ tailWord_2429644) baseStart_2429644 baseEnd_2429644 := by
    simpa [prefixWord, tailWord_2429644, baseEnd_2429644] using wordTrace_append hprefix tailTrace_2429644
  have hstable : (prefixWord ++ tailWord_2429644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429644).length < 2 ^ (prefixWord ++ tailWord_2429644).sum := by decide
  have hdescent : baseEnd_2429644 < baseStart_2429644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429663 : List Nat := [1, 1, 2, 3, 2, 5, 2, 2, 4]
def baseStart_2429663 : Nat := 118140960795 + 2429663 * 2 ^ 59
def prefixEnd_2429663 : Nat := 4983230072969 + 3 ^ 40 * 2429663 * 2
def baseEnd_2429663 : Nat := 277241099432229481341931

theorem tailTrace_2429663 : CollatzResearch.WordTrace tailWord_2429663 prefixEnd_2429663 277241099432229481341931 := by
  unfold tailWord_2429663
  simp only [CollatzResearch.WordTrace]
  refine ⟨88617089796753379249381643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59078059864502252832921095 88617089796753379249381643)
  ·
    refine ⟨132925634695130068874072465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88617089796753379249381643 132925634695130068874072465)
    ·
      refine ⟨99694226021347551655554349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132925634695130068874072465 99694226021347551655554349)
      ·
        refine ⟨37385334758005331870832881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99694226021347551655554349 37385334758005331870832881)
        ·
          refine ⟨28039001068503998903124661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37385334758005331870832881 28039001068503998903124661)
          ·
            refine ⟨2628656350172249897167937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28039001068503998903124661 2628656350172249897167937)
            ·
              refine ⟨1971492262629187422875953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2628656350172249897167937 1971492262629187422875953)
              ·
                refine ⟨1478619196971890567156965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1971492262629187422875953 1478619196971890567156965)
                ·
                  refine ⟨277241099432229481341931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1478619196971890567156965 277241099432229481341931)
                  ·
                    rfl

theorem cell22_2429663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 2, 4].length) (baseStart_2429663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429663 prefixEnd_2429663 := by exact prefixLift 2429663
  have htrace : WordTrace (prefixWord ++ tailWord_2429663) baseStart_2429663 baseEnd_2429663 := by
    simpa [prefixWord, tailWord_2429663, baseEnd_2429663] using wordTrace_append hprefix tailTrace_2429663
  have hstable : (prefixWord ++ tailWord_2429663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429663).length < 2 ^ (prefixWord ++ tailWord_2429663).sum := by decide
  have hdescent : baseEnd_2429663 < baseStart_2429663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429687 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 4, 6]
def baseStart_2429687 : Nat := 118140960795 + 2429687 * 2 ^ 59
def prefixEnd_2429687 : Nat := 4983230072969 + 3 ^ 40 * 2429687 * 2
def baseEnd_2429687 : Nat := 831731513987160381425719

theorem tailTrace_2429687 : CollatzResearch.WordTrace tailWord_2429687 prefixEnd_2429687 831731513987160381425719 := by
  unfold tailWord_2429687
  simp only [CollatzResearch.WordTrace]
  refine ⟨88617965148666431348255315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59078643432444287565503543 88617965148666431348255315)
  ·
    refine ⟨132926947722999647022382973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88617965148666431348255315 132926947722999647022382973)
    ·
      refine ⟨49847605396124867633393615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132926947722999647022382973 49847605396124867633393615)
      ·
        refine ⟨74771408094187301450090423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49847605396124867633393615 74771408094187301450090423)
        ·
          refine ⟨112157112141280952175135635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74771408094187301450090423 112157112141280952175135635)
          ·
            refine ⟨168235668211921428262703453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112157112141280952175135635 168235668211921428262703453)
            ·
              refine ⟨63088375579470535598513795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168235668211921428262703453 63088375579470535598513795)
              ·
                refine ⟨94632563369205803397770693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63088375579470535598513795 94632563369205803397770693)
                ·
                  refine ⟨17743605631726088137082005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94632563369205803397770693 17743605631726088137082005)
                  ·
                    refine ⟨831731513987160381425719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17743605631726088137082005 831731513987160381425719)
                    ·
                      rfl

theorem cell22_2429687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_2429687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429687 prefixEnd_2429687 := by exact prefixLift 2429687
  have htrace : WordTrace (prefixWord ++ tailWord_2429687) baseStart_2429687 baseEnd_2429687 := by
    simpa [prefixWord, tailWord_2429687, baseEnd_2429687] using wordTrace_append hprefix tailTrace_2429687
  have hstable : (prefixWord ++ tailWord_2429687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429687).length < 2 ^ (prefixWord ++ tailWord_2429687).sum := by decide
  have hdescent : baseEnd_2429687 < baseStart_2429687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429757 : List Nat := [1, 4, 1, 4, 2, 2, 1, 3, 1, 3]
def baseStart_2429757 : Nat := 118140960795 + 2429757 * 2 ^ 59
def prefixEnd_2429757 : Nat := 4983230072969 + 3 ^ 40 * 2429757 * 2
def baseEnd_2429757 : Nat := 831755476417703532175505

theorem tailTrace_2429757 : CollatzResearch.WordTrace tailWord_2429757 prefixEnd_2429757 831755476417703532175505 := by
  unfold tailWord_2429757
  simp only [CollatzResearch.WordTrace]
  refine ⟨88620518258412833303303525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59080345505608555535535683 88620518258412833303303525)
  ·
    refine ⟨16616347173452406244369411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88620518258412833303303525 16616347173452406244369411)
    ·
      refine ⟨24924520760178609366554117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16616347173452406244369411 24924520760178609366554117)
      ·
        refine ⟨4673347642533489256228897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24924520760178609366554117 4673347642533489256228897)
        ·
          refine ⟨3505010731900116942171673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4673347642533489256228897 3505010731900116942171673)
          ·
            refine ⟨2628758048925087706628755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3505010731900116942171673 2628758048925087706628755)
            ·
              refine ⟨3943137073387631559943133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2628758048925087706628755 3943137073387631559943133)
              ·
                refine ⟨1478676402520361834978675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3943137073387631559943133 1478676402520361834978675)
                ·
                  refine ⟨2218014603780542752468013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1478676402520361834978675 2218014603780542752468013)
                  ·
                    refine ⟨831755476417703532175505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2218014603780542752468013 831755476417703532175505)
                    ·
                      rfl

theorem cell22_2429757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_2429757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429757 prefixEnd_2429757 := by exact prefixLift 2429757
  have htrace : WordTrace (prefixWord ++ tailWord_2429757) baseStart_2429757 baseEnd_2429757 := by
    simpa [prefixWord, tailWord_2429757, baseEnd_2429757] using wordTrace_append hprefix tailTrace_2429757
  have hstable : (prefixWord ++ tailWord_2429757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429757).length < 2 ^ (prefixWord ++ tailWord_2429757).sum := by decide
  have hdescent : baseEnd_2429757 < baseStart_2429757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429809 : List Nat := [1, 2, 2, 2, 1, 4, 2, 8]
def baseStart_2429809 : Nat := 118140960795 + 2429809 * 2 ^ 59
def prefixEnd_2429809 : Nat := 4983230072969 + 3 ^ 40 * 2429809 * 2
def baseEnd_2429809 : Nat := 92419253008932525541705

theorem tailTrace_2429809 : CollatzResearch.WordTrace tailWord_2429809 prefixEnd_2429809 92419253008932525541705 := by
  unfold tailWord_2429809
  simp only [CollatzResearch.WordTrace]
  refine ⟨88622414854224446184196481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59081609902816297456130987 88622414854224446184196481)
  ·
    refine ⟨66466811140668334638147361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88622414854224446184196481 66466811140668334638147361)
    ·
      refine ⟨49850108355501250978610521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66466811140668334638147361 49850108355501250978610521)
      ·
        refine ⟨37387581266625938233957891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49850108355501250978610521 37387581266625938233957891)
        ·
          refine ⟨56081371899938907350936837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37387581266625938233957891 56081371899938907350936837)
          ·
            refine ⟨10515257231238545128300657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56081371899938907350936837 10515257231238545128300657)
            ·
              refine ⟨7886442923428908846225493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10515257231238545128300657 7886442923428908846225493)
              ·
                refine ⟨92419253008932525541705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7886442923428908846225493 92419253008932525541705)
                ·
                  rfl

theorem cell22_2429809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 8].length) (baseStart_2429809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429809 prefixEnd_2429809 := by exact prefixLift 2429809
  have htrace : WordTrace (prefixWord ++ tailWord_2429809) baseStart_2429809 baseEnd_2429809 := by
    simpa [prefixWord, tailWord_2429809, baseEnd_2429809] using wordTrace_append hprefix tailTrace_2429809
  have hstable : (prefixWord ++ tailWord_2429809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429809).length < 2 ^ (prefixWord ++ tailWord_2429809).sum := by decide
  have hdescent : baseEnd_2429809 < baseStart_2429809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429841 : List Nat := [1, 2, 2, 1, 1, 1, 3, 5, 3, 3]
def baseStart_2429841 : Nat := 118140960795 + 2429841 * 2 ^ 59
def prefixEnd_2429841 : Nat := 4983230072969 + 3 ^ 40 * 2429841 * 2
def baseEnd_2429841 : Nat := 831784231334355313075247

theorem tailTrace_2429841 : CollatzResearch.WordTrace tailWord_2429841 prefixEnd_2429841 831784231334355313075247 := by
  unfold tailWord_2429841
  simp only [CollatzResearch.WordTrace]
  refine ⟨88623581990108515649361377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59082387993405677099574251 88623581990108515649361377)
  ·
    refine ⟨66467686492581386737021033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88623581990108515649361377 66467686492581386737021033)
    ·
      refine ⟨49850764869436040052765775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66467686492581386737021033 49850764869436040052765775)
      ·
        refine ⟨74776147304154060079148663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49850764869436040052765775 74776147304154060079148663)
        ·
          refine ⟨112164220956231090118722995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74776147304154060079148663 112164220956231090118722995)
          ·
            refine ⟨168246331434346635178084493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112164220956231090118722995 168246331434346635178084493)
            ·
              refine ⟨63092374287879988191781685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168246331434346635178084493 63092374287879988191781685)
              ·
                refine ⟨5914910089488748892979533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63092374287879988191781685 5914910089488748892979533)
                ·
                  refine ⟨2218091283558280834867325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5914910089488748892979533 2218091283558280834867325)
                  ·
                    refine ⟨831784231334355313075247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2218091283558280834867325 831784231334355313075247)
                    ·
                      rfl

theorem cell22_2429841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3, 3].length) (baseStart_2429841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429841 prefixEnd_2429841 := by exact prefixLift 2429841
  have htrace : WordTrace (prefixWord ++ tailWord_2429841) baseStart_2429841 baseEnd_2429841 := by
    simpa [prefixWord, tailWord_2429841, baseEnd_2429841] using wordTrace_append hprefix tailTrace_2429841
  have hstable : (prefixWord ++ tailWord_2429841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429841).length < 2 ^ (prefixWord ++ tailWord_2429841).sum := by decide
  have hdescent : baseEnd_2429841 < baseStart_2429841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429858 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 5, 3]
def baseStart_2429858 : Nat := 118140960795 + 2429858 * 2 ^ 59
def prefixEnd_2429858 : Nat := 4983230072969 + 3 ^ 40 * 2429858 * 2
def baseEnd_2429858 : Nat := 831790050781772935400195

theorem tailTrace_2429858 : CollatzResearch.WordTrace tailWord_2429858 prefixEnd_2429858 831790050781772935400195 := by
  unfold tailWord_2429858
  simp only [CollatzResearch.WordTrace]
  refine ⟨22156050507761731888182557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59082801354031285035153485 22156050507761731888182557)
  ·
    refine ⟨8308518940410649458068459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22156050507761731888182557 8308518940410649458068459)
    ·
      refine ⟨12462778410615974187102689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8308518940410649458068459 12462778410615974187102689)
      ·
        refine ⟨9347083807961980640327017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12462778410615974187102689 9347083807961980640327017)
        ·
          refine ⟨7010312855971485480245263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9347083807961980640327017 7010312855971485480245263)
          ·
            refine ⟨10515469283957228220367895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7010312855971485480245263 10515469283957228220367895)
            ·
              refine ⟨15773203925935842330551843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10515469283957228220367895 15773203925935842330551843)
              ·
                refine ⟨23659805888903763495827765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15773203925935842330551843 23659805888903763495827765)
                ·
                  refine ⟨2218106802084727827733853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23659805888903763495827765 2218106802084727827733853)
                  ·
                    refine ⟨831790050781772935400195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2218106802084727827733853 831790050781772935400195)
                    ·
                      rfl

theorem cell22_2429858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_2429858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429858 prefixEnd_2429858 := by exact prefixLift 2429858
  have htrace : WordTrace (prefixWord ++ tailWord_2429858) baseStart_2429858 baseEnd_2429858 := by
    simpa [prefixWord, tailWord_2429858, baseEnd_2429858] using wordTrace_append hprefix tailTrace_2429858
  have hstable : (prefixWord ++ tailWord_2429858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429858).length < 2 ^ (prefixWord ++ tailWord_2429858).sum := by decide
  have hdescent : baseEnd_2429858 < baseStart_2429858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429886 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 4, 5]
def baseStart_2429886 : Nat := 118140960795 + 2429886 * 2 ^ 59
def prefixEnd_2429886 : Nat := 4983230072969 + 3 ^ 40 * 2429886 * 2
def baseEnd_2429886 : Nat := 831799635753990195700109

theorem tailTrace_2429886 : CollatzResearch.WordTrace tailWord_2429886 prefixEnd_2429886 831799635753990195700109 := by
  unfold tailWord_2429886
  simp only [CollatzResearch.WordTrace]
  refine ⟨11078152909368186041843689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59083482183296992223166341 11078152909368186041843689)
  ·
    refine ⟨8308614682026139531382767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11078152909368186041843689 8308614682026139531382767)
    ·
      refine ⟨12462922023039209297074151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8308614682026139531382767 12462922023039209297074151)
      ·
        refine ⟨18694383034558813945611227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12462922023039209297074151 18694383034558813945611227)
        ·
          refine ⟨28041574551838220918416841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18694383034558813945611227 28041574551838220918416841)
          ·
            refine ⟨21031180913878665688812631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28041574551838220918416841 21031180913878665688812631)
            ·
              refine ⟨31546771370817998533218947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21031180913878665688812631 31546771370817998533218947)
              ·
                refine ⟨47320157056226997799828421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31546771370817998533218947 47320157056226997799828421)
                ·
                  refine ⟨8872529448042562087467829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47320157056226997799828421 8872529448042562087467829)
                  ·
                    refine ⟨831799635753990195700109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8872529448042562087467829 831799635753990195700109)
                    ·
                      rfl

theorem cell22_2429886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_2429886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429886 prefixEnd_2429886 := by exact prefixLift 2429886
  have htrace : WordTrace (prefixWord ++ tailWord_2429886) baseStart_2429886 baseEnd_2429886 := by
    simpa [prefixWord, tailWord_2429886, baseEnd_2429886] using wordTrace_append hprefix tailTrace_2429886
  have hstable : (prefixWord ++ tailWord_2429886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429886).length < 2 ^ (prefixWord ++ tailWord_2429886).sum := by decide
  have hdescent : baseEnd_2429886 < baseStart_2429886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429888 : List Nat := [2, 1, 1, 2, 3, 5, 1, 2, 5]
def baseStart_2429888 : Nat := 118140960795 + 2429888 * 2 ^ 59
def prefixEnd_2429888 : Nat := 4983230072969 + 3 ^ 40 * 2429888 * 2
def baseEnd_2429888 : Nat := 277266773464954285716701

theorem tailTrace_2429888 : CollatzResearch.WordTrace tailWord_2429888 prefixEnd_2429888 277266773464954285716701 := by
  unfold tailWord_2429888
  simp only [CollatzResearch.WordTrace]
  refine ⟨44312648110469121338161159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59083530813958828450881545 44312648110469121338161159)
  ·
    refine ⟨66468972165703682007241739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44312648110469121338161159 66468972165703682007241739)
    ·
      refine ⟨99703458248555523010862609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66468972165703682007241739 99703458248555523010862609)
      ·
        refine ⟨74777593686416642258146957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99703458248555523010862609 74777593686416642258146957)
        ·
          refine ⟨28041597632406240846805109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74777593686416642258146957 28041597632406240846805109)
          ·
            refine ⟨2628899778038085079387979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28041597632406240846805109 2628899778038085079387979)
            ·
              refine ⟨3943349667057127619081969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2628899778038085079387979 3943349667057127619081969)
              ·
                refine ⟨2957512250292845714311477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3943349667057127619081969 2957512250292845714311477)
                ·
                  refine ⟨277266773464954285716701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2957512250292845714311477 277266773464954285716701)
                  ·
                    rfl

theorem cell22_2429888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 5].length) (baseStart_2429888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429888 prefixEnd_2429888 := by exact prefixLift 2429888
  have htrace : WordTrace (prefixWord ++ tailWord_2429888) baseStart_2429888 baseEnd_2429888 := by
    simpa [prefixWord, tailWord_2429888, baseEnd_2429888] using wordTrace_append hprefix tailTrace_2429888
  have hstable : (prefixWord ++ tailWord_2429888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429888).length < 2 ^ (prefixWord ++ tailWord_2429888).sum := by decide
  have hdescent : baseEnd_2429888 < baseStart_2429888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429892 : List Nat := [2, 3, 3, 3, 1, 1, 2, 1, 3, 3]
def baseStart_2429892 : Nat := 118140960795 + 2429892 * 2 ^ 59
def prefixEnd_2429892 : Nat := 4983230072969 + 3 ^ 40 * 2429892 * 2
def baseEnd_2429892 : Nat := 831801689676608180050091

theorem tailTrace_2429892 : CollatzResearch.WordTrace tailWord_2429892 prefixEnd_2429892 831801689676608180050091 := by
  unfold tailWord_2429892
  simp only [CollatzResearch.WordTrace]
  refine ⟨44312721056461875679733965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59083628075282500906311953 44312721056461875679733965)
  ·
    refine ⟨16617270396173203379900237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44312721056461875679733965 16617270396173203379900237)
    ·
      refine ⟨6231476398564951267462589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16617270396173203379900237 6231476398564951267462589)
      ·
        refine ⟨2336803649461856725298471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6231476398564951267462589 2336803649461856725298471)
        ·
          refine ⟨3505205474192785087947707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2336803649461856725298471 3505205474192785087947707)
          ·
            refine ⟨5257808211289177631921561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3505205474192785087947707 5257808211289177631921561)
            ·
              refine ⟨3943356158466883223941171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5257808211289177631921561 3943356158466883223941171)
              ·
                refine ⟨5915034237700324835911757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3943356158466883223941171 5915034237700324835911757)
                ·
                  refine ⟨2218137839137621813466909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5915034237700324835911757 2218137839137621813466909)
                  ·
                    refine ⟨831801689676608180050091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2218137839137621813466909 831801689676608180050091)
                    ·
                      rfl

theorem cell22_2429892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_2429892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429892 prefixEnd_2429892 := by exact prefixLift 2429892
  have htrace : WordTrace (prefixWord ++ tailWord_2429892) baseStart_2429892 baseEnd_2429892 := by
    simpa [prefixWord, tailWord_2429892, baseEnd_2429892] using wordTrace_append hprefix tailTrace_2429892
  have hstable : (prefixWord ++ tailWord_2429892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429892).length < 2 ^ (prefixWord ++ tailWord_2429892).sum := by decide
  have hdescent : baseEnd_2429892 < baseStart_2429892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429948 : List Nat := [2, 2, 2, 1, 2, 3, 2, 1, 4, 3]
def baseStart_2429948 : Nat := 118140960795 + 2429948 * 2 ^ 59
def prefixEnd_2429948 : Nat := 4983230072969 + 3 ^ 40 * 2429948 * 2
def baseEnd_2429948 : Nat := 831820859621042700649919

theorem tailTrace_2429948 : CollatzResearch.WordTrace tailWord_2429948 prefixEnd_2429948 831820859621042700649919 := by
  unfold tailWord_2429948
  simp only [CollatzResearch.WordTrace]
  refine ⟨44313742300360436461753249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59084989733813915282337665 44313742300360436461753249)
  ·
    refine ⟨33235306725270327346314937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44313742300360436461753249 33235306725270327346314937)
    ·
      refine ⟨24926480043952745509736203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33235306725270327346314937 24926480043952745509736203)
      ·
        refine ⟨37389720065929118264604305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24926480043952745509736203 37389720065929118264604305)
        ·
          refine ⟨28042290049446838698453229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37389720065929118264604305 28042290049446838698453229)
          ·
            refine ⟨10515858768542564511919961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28042290049446838698453229 10515858768542564511919961)
            ·
              refine ⟨7886894076406923383939971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10515858768542564511919961 7886894076406923383939971)
              ·
                refine ⟨11830341114610385075909957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7886894076406923383939971 11830341114610385075909957)
                ·
                  refine ⟨2218188958989447201733117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11830341114610385075909957 2218188958989447201733117)
                  ·
                    refine ⟨831820859621042700649919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2218188958989447201733117 831820859621042700649919)
                    ·
                      rfl

theorem cell22_2429948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_2429948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429948 prefixEnd_2429948 := by exact prefixLift 2429948
  have htrace : WordTrace (prefixWord ++ tailWord_2429948) baseStart_2429948 baseEnd_2429948 := by
    simpa [prefixWord, tailWord_2429948, baseEnd_2429948] using wordTrace_append hprefix tailTrace_2429948
  have hstable : (prefixWord ++ tailWord_2429948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429948).length < 2 ^ (prefixWord ++ tailWord_2429948).sum := by decide
  have hdescent : baseEnd_2429948 < baseStart_2429948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429980 : List Nat := [2, 2, 3, 1, 4, 1, 2, 1, 2, 4]
def baseStart_2429980 : Nat := 118140960795 + 2429980 * 2 ^ 59
def prefixEnd_2429980 : Nat := 4983230072969 + 3 ^ 40 * 2429980 * 2
def baseEnd_2429980 : Nat := 831831813875005283849821

theorem tailTrace_2429980 : CollatzResearch.WordTrace tailWord_2429980 prefixEnd_2429980 831831813875005283849821 := by
  unfold tailWord_2429980
  simp only [CollatzResearch.WordTrace]
  refine ⟨44314325868302471194335697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59085767824403294925780929 44314325868302471194335697)
  ·
    refine ⟨33235744401226853395751773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44314325868302471194335697 33235744401226853395751773)
    ·
      refine ⟨12463404150460070023406915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33235744401226853395751773 12463404150460070023406915)
      ·
        refine ⟨18695106225690105035110373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12463404150460070023406915 18695106225690105035110373)
        ·
          refine ⟨3505332417316894694083195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18695106225690105035110373 3505332417316894694083195)
          ·
            refine ⟨5257998625975342041124793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3505332417316894694083195 5257998625975342041124793)
            ·
              refine ⟨3943498969481506530843595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5257998625975342041124793 3943498969481506530843595)
              ·
                refine ⟨5915248454222259796265393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3943498969481506530843595 5915248454222259796265393)
                ·
                  refine ⟨4436436340666694847199045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5915248454222259796265393 4436436340666694847199045)
                  ·
                    refine ⟨831831813875005283849821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4436436340666694847199045 831831813875005283849821)
                    ·
                      rfl

theorem cell22_2429980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_2429980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2429980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2429980 prefixEnd_2429980 := by exact prefixLift 2429980
  have htrace : WordTrace (prefixWord ++ tailWord_2429980) baseStart_2429980 baseEnd_2429980 := by
    simpa [prefixWord, tailWord_2429980, baseEnd_2429980] using wordTrace_append hprefix tailTrace_2429980
  have hstable : (prefixWord ++ tailWord_2429980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429980).length < 2 ^ (prefixWord ++ tailWord_2429980).sum := by decide
  have hdescent : baseEnd_2429980 < baseStart_2429980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430021 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 1, 7]
def baseStart_2430021 : Nat := 118140960795 + 2430021 * 2 ^ 59
def prefixEnd_2430021 : Nat := 4983230072969 + 3 ^ 40 * 2430021 * 2
def baseEnd_2430021 : Nat := 831845849012894843574695

theorem tailTrace_2430021 : CollatzResearch.WordTrace tailWord_2430021 prefixEnd_2430021 831845849012894843574695 := by
  unfold tailWord_2430021
  simp only [CollatzResearch.WordTrace]
  refine ⟨88630147129456406390913917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59086764752970937593942611 88630147129456406390913917)
  ·
    refine ⟨33236305173546152396592719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88630147129456406390913917 33236305173546152396592719)
    ·
      refine ⟨49854457760319228594889079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33236305173546152396592719 49854457760319228594889079)
      ·
        refine ⟨74781686640478842892333619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49854457760319228594889079 74781686640478842892333619)
        ·
          refine ⟨112172529960718264338500429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74781686640478842892333619 112172529960718264338500429)
          ·
            refine ⟨42064698735269349126937661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112172529960718264338500429 42064698735269349126937661)
            ·
              refine ⟨15774262025726005922601623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42064698735269349126937661 15774262025726005922601623)
              ·
                refine ⟨23661393038589008883902435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15774262025726005922601623 23661393038589008883902435)
                ·
                  refine ⟨35492089557883513325853653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23661393038589008883902435 35492089557883513325853653)
                  ·
                    refine ⟨831845849012894843574695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35492089557883513325853653 831845849012894843574695)
                    ·
                      rfl

theorem cell22_2430021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_2430021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2430021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2430021 prefixEnd_2430021 := by exact prefixLift 2430021
  have htrace : WordTrace (prefixWord ++ tailWord_2430021) baseStart_2430021 baseEnd_2430021 := by
    simpa [prefixWord, tailWord_2430021, baseEnd_2430021] using wordTrace_append hprefix tailTrace_2430021
  have hstable : (prefixWord ++ tailWord_2430021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430021).length < 2 ^ (prefixWord ++ tailWord_2430021).sum := by decide
  have hdescent : baseEnd_2430021 < baseStart_2430021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430023 : List Nat := [1, 1, 4, 1, 3, 2, 2, 3, 5]
def baseStart_2430023 : Nat := 118140960795 + 2430023 * 2 ^ 59
def prefixEnd_2430023 : Nat := 4983230072969 + 3 ^ 40 * 2430023 * 2
def baseEnd_2430023 : Nat := 277282177884589168341563

theorem tailTrace_2430023 : CollatzResearch.WordTrace tailWord_2430023 prefixEnd_2430023 277282177884589168341563 := by
  unfold tailWord_2430023
  simp only [CollatzResearch.WordTrace]
  refine ⟨88630220075449160732486723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59086813383632773821657815 88630220075449160732486723)
  ·
    refine ⟨132945330113173741098730085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88630220075449160732486723 132945330113173741098730085)
    ·
      refine ⟨24927249396220076456011891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132945330113173741098730085 24927249396220076456011891)
      ·
        refine ⟨37390874094330114684017837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24927249396220076456011891 37390874094330114684017837)
        ·
          refine ⟨14021577785373793006506689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37390874094330114684017837 14021577785373793006506689)
          ·
            refine ⟨10516183339030344754880017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14021577785373793006506689 10516183339030344754880017)
            ·
              refine ⟨7887137504272758566160013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10516183339030344754880017 7887137504272758566160013)
              ·
                refine ⟨2957676564102284462310005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7887137504272758566160013 2957676564102284462310005)
                ·
                  refine ⟨277282177884589168341563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2957676564102284462310005 277282177884589168341563)
                  ·
                    rfl

theorem cell22_2430023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 5].length) (baseStart_2430023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2430023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2430023 prefixEnd_2430023 := by exact prefixLift 2430023
  have htrace : WordTrace (prefixWord ++ tailWord_2430023) baseStart_2430023 baseEnd_2430023 := by
    simpa [prefixWord, tailWord_2430023, baseEnd_2430023] using wordTrace_append hprefix tailTrace_2430023
  have hstable : (prefixWord ++ tailWord_2430023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430023).length < 2 ^ (prefixWord ++ tailWord_2430023).sum := by decide
  have hdescent : baseEnd_2430023 < baseStart_2430023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430051 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 10]
def baseStart_2430051 : Nat := 118140960795 + 2430051 * 2 ^ 59
def prefixEnd_2430051 : Nat := 4983230072969 + 3 ^ 40 * 2430051 * 2
def baseEnd_2430051 : Nat := 277285372875328255108201

theorem tailTrace_2430051 : CollatzResearch.WordTrace tailWord_2430051 prefixEnd_2430051 277285372875328255108201 := by
  unfold tailWord_2430051
  simp only [CollatzResearch.WordTrace]
  refine ⟨88631241319347721514506007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59087494212898481009670671 88631241319347721514506007)
  ·
    refine ⟨132946861979021582271759011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88631241319347721514506007 132946861979021582271759011)
    ·
      refine ⟨199420292968532373407638517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132946861979021582271759011 199420292968532373407638517)
      ·
        refine ⟨18695652465799910006966111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 199420292968532373407638517 18695652465799910006966111)
        ·
          refine ⟨28043478698699865010449167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18695652465799910006966111 28043478698699865010449167)
          ·
            refine ⟨42065218048049797515673751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28043478698699865010449167 42065218048049797515673751)
            ·
              refine ⟨63097827072074696273510627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42065218048049797515673751 63097827072074696273510627)
              ·
                refine ⟨94646740608112044410265941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63097827072074696273510627 94646740608112044410265941)
                ·
                  refine ⟨277285372875328255108201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 94646740608112044410265941 277285372875328255108201)
                  ·
                    rfl

theorem cell22_2430051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 10].length) (baseStart_2430051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2430051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2430051 prefixEnd_2430051 := by exact prefixLift 2430051
  have htrace : WordTrace (prefixWord ++ tailWord_2430051) baseStart_2430051 baseEnd_2430051 := by
    simpa [prefixWord, tailWord_2430051, baseEnd_2430051] using wordTrace_append hprefix tailTrace_2430051
  have hstable : (prefixWord ++ tailWord_2430051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430051).length < 2 ^ (prefixWord ++ tailWord_2430051).sum := by decide
  have hdescent : baseEnd_2430051 < baseStart_2430051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430119 : List Nat := [1, 1, 6, 2, 1, 2, 3, 2, 4]
def baseStart_2430119 : Nat := 118140960795 + 2430119 * 2 ^ 59
def prefixEnd_2430119 : Nat := 4983230072969 + 3 ^ 40 * 2430119 * 2
def baseEnd_2430119 : Nat := 277293132138551751541465

theorem tailTrace_2430119 : CollatzResearch.WordTrace tailWord_2430119 prefixEnd_2430119 277293132138551751541465 := by
  unfold tailWord_2430119
  simp only [CollatzResearch.WordTrace]
  refine ⟨88633721483101369127981411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59089147655400912751987607 88633721483101369127981411)
  ·
    refine ⟨132950582224652053691972117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88633721483101369127981411 132950582224652053691972117)
    ·
      refine ⟨6232058541780565016811193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 132950582224652053691972117 6232058541780565016811193)
      ·
        refine ⟨4674043906335423762608395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6232058541780565016811193 4674043906335423762608395)
        ·
          refine ⟨7011065859503135643912593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4674043906335423762608395 7011065859503135643912593)
          ·
            refine ⟨5258299394627351732934445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7011065859503135643912593 5258299394627351732934445)
            ·
              refine ⟨1971862272985256899850417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5258299394627351732934445 1971862272985256899850417)
              ·
                refine ⟨1478896704738942674887813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1971862272985256899850417 1478896704738942674887813)
                ·
                  refine ⟨277293132138551751541465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1478896704738942674887813 277293132138551751541465)
                  ·
                    rfl

theorem cell22_2430119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 2, 4].length) (baseStart_2430119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2430119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2430119 prefixEnd_2430119 := by exact prefixLift 2430119
  have htrace : WordTrace (prefixWord ++ tailWord_2430119) baseStart_2430119 baseEnd_2430119 := by
    simpa [prefixWord, tailWord_2430119, baseEnd_2430119] using wordTrace_append hprefix tailTrace_2430119
  have hstable : (prefixWord ++ tailWord_2430119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430119).length < 2 ^ (prefixWord ++ tailWord_2430119).sum := by decide
  have hdescent : baseEnd_2430119 < baseStart_2430119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430222 : List Nat := [4, 1, 1, 2, 1, 4, 1, 3, 1, 4]
def baseStart_2430222 : Nat := 118140960795 + 2430222 * 2 ^ 59
def prefixEnd_2430222 : Nat := 4983230072969 + 3 ^ 40 * 2430222 * 2
def baseEnd_2430222 : Nat := 831914655420597319299079

theorem tailTrace_2430222 : CollatzResearch.WordTrace tailWord_2430222 prefixEnd_2430222 831914655420597319299079 := by
  unfold tailWord_2430222
  simp only [CollatzResearch.WordTrace]
  refine ⟨11079684775216027214872615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59091652134485478479320613 11079684775216027214872615)
  ·
    refine ⟨16619527162824040822308923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11079684775216027214872615 16619527162824040822308923)
    ·
      refine ⟨24929290744236061233463385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16619527162824040822308923 24929290744236061233463385)
      ·
        refine ⟨18696968058177045925097539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24929290744236061233463385 18696968058177045925097539)
        ·
          refine ⟨28045452087265568887646309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18696968058177045925097539 28045452087265568887646309)
          ·
            refine ⟨5258522266362294166433683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28045452087265568887646309 5258522266362294166433683)
            ·
              refine ⟨7887783399543441249650525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5258522266362294166433683 7887783399543441249650525)
              ·
                refine ⟨2957918774828790468618947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7887783399543441249650525 2957918774828790468618947)
                ·
                  refine ⟨4436878162243185702928421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2957918774828790468618947 4436878162243185702928421)
                  ·
                    refine ⟨831914655420597319299079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4436878162243185702928421 831914655420597319299079)
                    ·
                      rfl

theorem cell22_2430222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_2430222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2430222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2430222 prefixEnd_2430222 := by exact prefixLift 2430222
  have htrace : WordTrace (prefixWord ++ tailWord_2430222) baseStart_2430222 baseEnd_2430222 := by
    simpa [prefixWord, tailWord_2430222, baseEnd_2430222] using wordTrace_append hprefix tailTrace_2430222
  have hstable : (prefixWord ++ tailWord_2430222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430222).length < 2 ^ (prefixWord ++ tailWord_2430222).sum := by decide
  have hdescent : baseEnd_2430222 < baseStart_2430222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430226 : List Nat := [3, 2, 4, 2, 1, 2, 1, 2, 5]
def baseStart_2430226 : Nat := 118140960795 + 2430226 * 2 ^ 59
def prefixEnd_2430226 : Nat := 4983230072969 + 3 ^ 40 * 2430226 * 2
def baseEnd_2430226 : Nat := 277305341567447547399689

theorem tailTrace_2430226 : CollatzResearch.WordTrace tailWord_2430226 prefixEnd_2430226 277305341567447547399689 := by
  unfold tailWord_2430226
  simp only [CollatzResearch.WordTrace]
  refine ⟨22159406023428431600531633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59091749395809150934751021 22159406023428431600531633)
  ·
    refine ⟨16619554517571323700398725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22159406023428431600531633 16619554517571323700398725)
    ·
      refine ⟨3116166472044623193824761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16619554517571323700398725 3116166472044623193824761)
      ·
        refine ⟨2337124854033467395368571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3116166472044623193824761 2337124854033467395368571)
        ·
          refine ⟨3505687281050201093052857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2337124854033467395368571 3505687281050201093052857)
          ·
            refine ⟨2629265460787650819789643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3505687281050201093052857 2629265460787650819789643)
            ·
              refine ⟨3943898191181476229684465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2629265460787650819789643 3943898191181476229684465)
              ·
                refine ⟨2957923643386107172263349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3943898191181476229684465 2957923643386107172263349)
                ·
                  refine ⟨277305341567447547399689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2957923643386107172263349 277305341567447547399689)
                  ·
                    rfl

theorem cell22_2430226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_2430226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2430226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2430226 prefixEnd_2430226 := by exact prefixLift 2430226
  have htrace : WordTrace (prefixWord ++ tailWord_2430226) baseStart_2430226 baseEnd_2430226 := by
    simpa [prefixWord, tailWord_2430226, baseEnd_2430226] using wordTrace_append hprefix tailTrace_2430226
  have hstable : (prefixWord ++ tailWord_2430226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430226).length < 2 ^ (prefixWord ++ tailWord_2430226).sum := by decide
  have hdescent : baseEnd_2430226 < baseStart_2430226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430237 : List Nat := [1, 4, 2, 3, 1, 2, 2, 1, 6]
def baseStart_2430237 : Nat := 118140960795 + 2430237 * 2 ^ 59
def prefixEnd_2430237 : Nat := 4983230072969 + 3 ^ 40 * 2430237 * 2
def baseEnd_2430237 : Nat := 277306596742380760058011

theorem tailTrace_2430237 : CollatzResearch.WordTrace tailWord_2430237 prefixEnd_2430237 277306596742380760058011 := by
  unfold tailWord_2430237
  simp only [CollatzResearch.WordTrace]
  refine ⟨88638025296673875280776965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59092016864449250187184643 88638025296673875280776965)
  ·
    refine ⟨16619629743126351615145681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88638025296673875280776965 16619629743126351615145681)
    ·
      refine ⟨12464722307344763711359261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16619629743126351615145681 12464722307344763711359261)
      ·
        refine ⟨4674270865254286391759723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12464722307344763711359261 4674270865254286391759723)
        ·
          refine ⟨7011406297881429587639585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4674270865254286391759723 7011406297881429587639585)
          ·
            refine ⟨5258554723411072190729689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7011406297881429587639585 5258554723411072190729689)
            ·
              refine ⟨3943916042558304143047267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5258554723411072190729689 3943916042558304143047267)
              ·
                refine ⟨5915874063837456214570901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3943916042558304143047267 5915874063837456214570901)
                ·
                  refine ⟨277306596742380760058011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5915874063837456214570901 277306596742380760058011)
                  ·
                    rfl

theorem cell22_2430237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_2430237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2430237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2430237 prefixEnd_2430237 := by exact prefixLift 2430237
  have htrace : WordTrace (prefixWord ++ tailWord_2430237) baseStart_2430237 baseEnd_2430237 := by
    simpa [prefixWord, tailWord_2430237, baseEnd_2430237] using wordTrace_append hprefix tailTrace_2430237
  have hstable : (prefixWord ++ tailWord_2430237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430237).length < 2 ^ (prefixWord ++ tailWord_2430237).sum := by decide
  have hdescent : baseEnd_2430237 < baseStart_2430237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430297 : List Nat := [1, 2, 1, 2, 2, 2, 5, 1, 3, 3]
def baseStart_2430297 : Nat := 118140960795 + 2430297 * 2 ^ 59
def prefixEnd_2430297 : Nat := 4983230072969 + 3 ^ 40 * 2430297 * 2
def baseEnd_2430297 : Nat := 831940329453322123673849

theorem tailTrace_2430297 : CollatzResearch.WordTrace tailWord_2430297 prefixEnd_2430297 831940329453322123673849 := by
  unfold tailWord_2430297
  simp only [CollatzResearch.WordTrace]
  refine ⟨88640213676456505527961145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59093475784304337018640763 88640213676456505527961145)
  ·
    refine ⟨66480160257342379145970859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88640213676456505527961145 66480160257342379145970859)
    ·
      refine ⟨99720240386013568718956289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66480160257342379145970859 99720240386013568718956289)
      ·
        refine ⟨74790180289510176539217217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99720240386013568718956289 74790180289510176539217217)
        ·
          refine ⟨56092635217132632404412913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74790180289510176539217217 56092635217132632404412913)
          ·
            refine ⟨42069476412849474303309685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56092635217132632404412913 42069476412849474303309685)
            ·
              refine ⟨3944013413704638215935283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42069476412849474303309685 3944013413704638215935283)
              ·
                refine ⟨5916020120556957323902925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3944013413704638215935283 5916020120556957323902925)
                ·
                  refine ⟨2218507545208858996463597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5916020120556957323902925 2218507545208858996463597)
                  ·
                    refine ⟨831940329453322123673849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2218507545208858996463597 831940329453322123673849)
                    ·
                      rfl

theorem cell22_2430297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 3, 3].length) (baseStart_2430297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2430297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2430297 prefixEnd_2430297 := by exact prefixLift 2430297
  have htrace : WordTrace (prefixWord ++ tailWord_2430297) baseStart_2430297 baseEnd_2430297 := by
    simpa [prefixWord, tailWord_2430297, baseEnd_2430297] using wordTrace_append hprefix tailTrace_2430297
  have hstable : (prefixWord ++ tailWord_2430297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430297).length < 2 ^ (prefixWord ++ tailWord_2430297).sum := by decide
  have hdescent : baseEnd_2430297 < baseStart_2430297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430389 : List Nat := [1, 3, 3, 2, 2, 1, 1, 5, 4]
def baseStart_2430389 : Nat := 118140960795 + 2430389 * 2 ^ 59
def prefixEnd_2430389 : Nat := 4983230072969 + 3 ^ 40 * 2430389 * 2
def baseEnd_2430389 : Nat := 277323940977821516791189

theorem tailTrace_2430389 : CollatzResearch.WordTrace tailWord_2430389 prefixEnd_2430389 277323940977821516791189 := by
  unfold tailWord_2430389
  simp only [CollatzResearch.WordTrace]
  refine ⟨88643569192123205240310221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59095712794748803493540147 88643569192123205240310221)
  ·
    refine ⟨33241338447046201965116333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88643569192123205240310221 33241338447046201965116333)
    ·
      refine ⟨12465501917642325736918625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33241338447046201965116333 12465501917642325736918625)
      ·
        refine ⟨9349126438231744302688969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12465501917642325736918625 9349126438231744302688969)
        ·
          refine ⟨7011844828673808227016727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9349126438231744302688969 7011844828673808227016727)
          ·
            refine ⟨10517767243010712340525091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7011844828673808227016727 10517767243010712340525091)
            ·
              refine ⟨15776650864516068510787637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10517767243010712340525091 15776650864516068510787637)
              ·
                refine ⟨1479061018548381422886341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15776650864516068510787637 1479061018548381422886341)
                ·
                  refine ⟨277323940977821516791189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1479061018548381422886341 277323940977821516791189)
                  ·
                    rfl

theorem cell22_2430389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5, 4].length) (baseStart_2430389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2430389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2430389 prefixEnd_2430389 := by exact prefixLift 2430389
  have htrace : WordTrace (prefixWord ++ tailWord_2430389) baseStart_2430389 baseEnd_2430389 := by
    simpa [prefixWord, tailWord_2430389, baseEnd_2430389] using wordTrace_append hprefix tailTrace_2430389
  have hstable : (prefixWord ++ tailWord_2430389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430389).length < 2 ^ (prefixWord ++ tailWord_2430389).sum := by decide
  have hdescent : baseEnd_2430389 < baseStart_2430389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430421 : List Nat := [1, 3, 2, 3, 1, 1, 5, 1, 2, 3]
def baseStart_2430421 : Nat := 118140960795 + 2430421 * 2 ^ 59
def prefixEnd_2430421 : Nat := 4983230072969 + 3 ^ 40 * 2430421 * 2
def baseEnd_2430421 : Nat := 831982777187427133573469

theorem tailTrace_2430421 : CollatzResearch.WordTrace tailWord_2430421 prefixEnd_2430421 831982777187427133573469 := by
  unfold tailWord_2430421
  simp only [CollatzResearch.WordTrace]
  refine ⟨88644736328007274705475117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59096490885338183136983411 88644736328007274705475117)
  ·
    refine ⟨33241776123002728014553169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88644736328007274705475117 33241776123002728014553169)
    ·
      refine ⟨24931332092252046010914877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33241776123002728014553169 24931332092252046010914877)
      ·
        refine ⟨9349249534594517254093079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24931332092252046010914877 9349249534594517254093079)
        ·
          refine ⟨14023874301891775881139619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9349249534594517254093079 14023874301891775881139619)
          ·
            refine ⟨21035811452837663821709429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14023874301891775881139619 21035811452837663821709429)
            ·
              refine ⟨1972107323703530983285259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21035811452837663821709429 1972107323703530983285259)
              ·
                refine ⟨2958160985555296474927889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1972107323703530983285259 2958160985555296474927889)
                ·
                  refine ⟨2218620739166472356195917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2958160985555296474927889 2218620739166472356195917)
                  ·
                    refine ⟨831982777187427133573469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2218620739166472356195917 831982777187427133573469)
                    ·
                      rfl

theorem cell22_2430421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_2430421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2430421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2430421 prefixEnd_2430421 := by exact prefixLift 2430421
  have htrace : WordTrace (prefixWord ++ tailWord_2430421) baseStart_2430421 baseEnd_2430421 := by
    simpa [prefixWord, tailWord_2430421, baseEnd_2430421] using wordTrace_append hprefix tailTrace_2430421
  have hstable : (prefixWord ++ tailWord_2430421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430421).length < 2 ^ (prefixWord ++ tailWord_2430421).sum := by decide
  have hdescent : baseEnd_2430421 < baseStart_2430421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430432 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 5, 3]
def baseStart_2430432 : Nat := 118140960795 + 2430432 * 2 ^ 59
def prefixEnd_2430432 : Nat := 4983230072969 + 3 ^ 40 * 2430432 * 2
def baseEnd_2430432 : Nat := 831986542712226771548435

theorem tailTrace_2430432 : CollatzResearch.WordTrace tailWord_2430432 prefixEnd_2430432 831986542712226771548435 := by
  unfold tailWord_2430432
  simp only [CollatzResearch.WordTrace]
  refine ⟨44322568765483711792062775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59096758353978282389417033 44322568765483711792062775)
  ·
    refine ⟨66483853148225567688094163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44322568765483711792062775 66483853148225567688094163)
    ·
      refine ⟨99725779722338351532141245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66483853148225567688094163 99725779722338351532141245)
      ·
        refine ⟨37397167395876881824552967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99725779722338351532141245 37397167395876881824552967)
        ·
          refine ⟨56095751093815322736829451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37397167395876881824552967 56095751093815322736829451)
          ·
            refine ⟨84143626640722984105244177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56095751093815322736829451 84143626640722984105244177)
            ·
              refine ⟨63107719980542238078933133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84143626640722984105244177 63107719980542238078933133)
              ·
                refine ⟨23665394992703339279599925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63107719980542238078933133 23665394992703339279599925)
                ·
                  refine ⟨2218630780565938057462493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23665394992703339279599925 2218630780565938057462493)
                  ·
                    refine ⟨831986542712226771548435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2218630780565938057462493 831986542712226771548435)
                    ·
                      rfl

theorem cell22_2430432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 5, 3].length) (baseStart_2430432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2430432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2430432 prefixEnd_2430432 := by exact prefixLift 2430432
  have htrace : WordTrace (prefixWord ++ tailWord_2430432) baseStart_2430432 baseEnd_2430432 := by
    simpa [prefixWord, tailWord_2430432, baseEnd_2430432] using wordTrace_append hprefix tailTrace_2430432
  have hstable : (prefixWord ++ tailWord_2430432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430432).length < 2 ^ (prefixWord ++ tailWord_2430432).sum := by decide
  have hdescent : baseEnd_2430432 < baseStart_2430432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430522 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 3, 5]
def baseStart_2430522 : Nat := 118140960795 + 2430522 * 2 ^ 59
def prefixEnd_2430522 : Nat := 4983230072969 + 3 ^ 40 * 2430522 * 2
def baseEnd_2430522 : Nat := 832017351551496536798159

theorem tailTrace_2430522 : CollatzResearch.WordTrace tailWord_2430522 prefixEnd_2430522 832017351551496536798159 := by
  unfold tailWord_2430522
  simp only [CollatzResearch.WordTrace]
  refine ⟨22162105025160342238725455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59098946733760912636601213 22162105025160342238725455)
  ·
    refine ⟨33243157537740513358088183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22162105025160342238725455 33243157537740513358088183)
    ·
      refine ⟨49864736306610770037132275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33243157537740513358088183 49864736306610770037132275)
      ·
        refine ⟨74797104459916155055698413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49864736306610770037132275 74797104459916155055698413)
        ·
          refine ⟨28048914172468558145886905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74797104459916155055698413 28048914172468558145886905)
          ·
            refine ⟨21036685629351418609415179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28048914172468558145886905 21036685629351418609415179)
            ·
              refine ⟨31555028444027127914122769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21036685629351418609415179 31555028444027127914122769)
              ·
                refine ⟨23666271333020345935592077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31555028444027127914122769 23666271333020345935592077)
                ·
                  refine ⟨8874851749882629725847029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23666271333020345935592077 8874851749882629725847029)
                  ·
                    refine ⟨832017351551496536798159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8874851749882629725847029 832017351551496536798159)
                    ·
                      rfl

theorem cell22_2430522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_2430522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2430522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2430522 prefixEnd_2430522 := by exact prefixLift 2430522
  have htrace : WordTrace (prefixWord ++ tailWord_2430522) baseStart_2430522 baseEnd_2430522 := by
    simpa [prefixWord, tailWord_2430522, baseEnd_2430522] using wordTrace_append hprefix tailTrace_2430522
  have hstable : (prefixWord ++ tailWord_2430522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430522).length < 2 ^ (prefixWord ++ tailWord_2430522).sum := by decide
  have hdescent : baseEnd_2430522 < baseStart_2430522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430537 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 4, 4]
def baseStart_2430537 : Nat := 118140960795 + 2430537 * 2 ^ 59
def prefixEnd_2430537 : Nat := 4983230072969 + 3 ^ 40 * 2430537 * 2
def baseEnd_2430537 : Nat := 832022486358041497673113

theorem tailTrace_2430537 : CollatzResearch.WordTrace tailWord_2430537 prefixEnd_2430537 832022486358041497673113 := by
  unfold tailWord_2430537
  simp only [CollatzResearch.WordTrace]
  refine ⟨88648967195587026516697865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59099311463724684344465243 88648967195587026516697865)
  ·
    refine ⟨66486725396690269887523399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88648967195587026516697865 66486725396690269887523399)
    ·
      refine ⟨99730088095035404831285099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66486725396690269887523399 99730088095035404831285099)
      ·
        refine ⟨149595132142553107246927649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99730088095035404831285099 149595132142553107246927649)
        ·
          refine ⟨112196349106914830435195737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149595132142553107246927649 112196349106914830435195737)
          ·
            refine ⟨84147261830186122826396803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112196349106914830435195737 84147261830186122826396803)
            ·
              refine ⟨126220892745279184239595205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84147261830186122826396803 126220892745279184239595205)
              ·
                refine ⟨23666417389739847044924101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126220892745279184239595205 23666417389739847044924101)
                ·
                  refine ⟨4437453260576221320923269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23666417389739847044924101 4437453260576221320923269)
                  ·
                    refine ⟨832022486358041497673113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4437453260576221320923269 832022486358041497673113)
                    ·
                      rfl

theorem cell22_2430537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 4].length) (baseStart_2430537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2430537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2430537 prefixEnd_2430537 := by exact prefixLift 2430537
  have htrace : WordTrace (prefixWord ++ tailWord_2430537) baseStart_2430537 baseEnd_2430537 := by
    simpa [prefixWord, tailWord_2430537, baseEnd_2430537] using wordTrace_append hprefix tailTrace_2430537
  have hstable : (prefixWord ++ tailWord_2430537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430537).length < 2 ^ (prefixWord ++ tailWord_2430537).sum := by decide
  have hdescent : baseEnd_2430537 < baseStart_2430537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430541 : List Nat := [1, 6, 1, 1, 3, 1, 1, 2, 6]
def baseStart_2430541 : Nat := 118140960795 + 2430541 * 2 ^ 59
def prefixEnd_2430541 : Nat := 4983230072969 + 3 ^ 40 * 2430541 * 2
def baseEnd_2430541 : Nat := 277341285213262273524367

theorem tailTrace_2430541 : CollatzResearch.WordTrace tailWord_2430541 prefixEnd_2430541 277341285213262273524367 := by
  unfold tailWord_2430541
  simp only [CollatzResearch.WordTrace]
  refine ⟨88649113087572535199843477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59099408725048356799895651 88649113087572535199843477)
  ·
    refine ⟨4155427175979962587492663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 88649113087572535199843477 4155427175979962587492663)
    ·
      refine ⟨6233140763969943881238995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4155427175979962587492663 6233140763969943881238995)
      ·
        refine ⟨9349711145954915821858493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6233140763969943881238995 9349711145954915821858493)
        ·
          refine ⟨3506141679733093433196935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9349711145954915821858493 3506141679733093433196935)
          ·
            refine ⟨5259212519599640149795403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3506141679733093433196935 5259212519599640149795403)
            ·
              refine ⟨7888818779399460224693105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5259212519599640149795403 7888818779399460224693105)
              ·
                refine ⟨5916614084549595168519829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7888818779399460224693105 5916614084549595168519829)
                ·
                  refine ⟨277341285213262273524367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5916614084549595168519829 277341285213262273524367)
                  ·
                    rfl

theorem cell22_2430541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_2430541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2430541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2430541 prefixEnd_2430541 := by exact prefixLift 2430541
  have htrace : WordTrace (prefixWord ++ tailWord_2430541) baseStart_2430541 baseEnd_2430541 := by
    simpa [prefixWord, tailWord_2430541, baseEnd_2430541] using wordTrace_append hprefix tailTrace_2430541
  have hstable : (prefixWord ++ tailWord_2430541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430541).length < 2 ^ (prefixWord ++ tailWord_2430541).sum := by decide
  have hdescent : baseEnd_2430541 < baseStart_2430541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430753 : List Nat := [1, 2, 3, 2, 1, 4, 2, 1, 3, 3]
def baseStart_2430753 : Nat := 118140960795 + 2430753 * 2 ^ 59
def prefixEnd_2430753 : Nat := 4983230072969 + 3 ^ 40 * 2430753 * 2
def baseEnd_2430753 : Nat := 832096427572288934272451

theorem tailTrace_2430753 : CollatzResearch.WordTrace tailWord_2430753 prefixEnd_2430753 832096427572288934272451 := by
  unfold tailWord_2430753
  simp only [CollatzResearch.WordTrace]
  refine ⟨88656845362804495406560913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59104563575202996937707275 88656845362804495406560913)
  ·
    refine ⟨66492634022103371554920685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88656845362804495406560913 66492634022103371554920685)
    ·
      refine ⟨24934737758288764333095257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66492634022103371554920685 24934737758288764333095257)
      ·
        refine ⟨18701053318716573249821443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24934737758288764333095257 18701053318716573249821443)
        ·
          refine ⟨28051579978074859874732165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18701053318716573249821443 28051579978074859874732165)
          ·
            refine ⟨5259671245889036226512281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28051579978074859874732165 5259671245889036226512281)
            ·
              refine ⟨3944753434416777169884211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5259671245889036226512281 3944753434416777169884211)
              ·
                refine ⟨5917130151625165754826317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3944753434416777169884211 5917130151625165754826317)
                ·
                  refine ⟨2218923806859437158059869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5917130151625165754826317 2218923806859437158059869)
                  ·
                    refine ⟨832096427572288934272451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2218923806859437158059869 832096427572288934272451)
                    ·
                      rfl

theorem cell22_2430753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_2430753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2430753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2430753 prefixEnd_2430753 := by exact prefixLift 2430753
  have htrace : WordTrace (prefixWord ++ tailWord_2430753) baseStart_2430753 baseEnd_2430753 := by
    simpa [prefixWord, tailWord_2430753, baseEnd_2430753] using wordTrace_append hprefix tailTrace_2430753
  have hstable : (prefixWord ++ tailWord_2430753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430753).length < 2 ^ (prefixWord ++ tailWord_2430753).sum := by decide
  have hdescent : baseEnd_2430753 < baseStart_2430753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430830 : List Nat := [4, 1, 2, 3, 1, 1, 3, 2, 1, 4]
def baseStart_2430830 : Nat := 118140960795 + 2430830 * 2 ^ 59
def prefixEnd_2430830 : Nat := 4983230072969 + 3 ^ 40 * 2430830 * 2
def baseEnd_2430830 : Nat := 832122786245886400097215

theorem tailTrace_2430830 : CollatzResearch.WordTrace tailWord_2430830 prefixEnd_2430830 832122786245886400097215 := by
  unfold tailWord_2430830
  simp only [CollatzResearch.WordTrace]
  refine ⟨11082456722940692194639243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59106435855683691704742629 11082456722940692194639243)
  ·
    refine ⟨16623685084411038291958865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11082456722940692194639243 16623685084411038291958865)
    ·
      refine ⟨12467763813308278718969149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16623685084411038291958865 12467763813308278718969149)
      ·
        refine ⟨4675411429990604519613431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12467763813308278718969149 4675411429990604519613431)
        ·
          refine ⟨7013117144985906779420147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4675411429990604519613431 7013117144985906779420147)
          ·
            refine ⟨10519675717478860169130221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7013117144985906779420147 10519675717478860169130221)
            ·
              refine ⟨3944878394054572563423833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10519675717478860169130221 3944878394054572563423833)
              ·
                refine ⟨2958658795540929422567875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3944878394054572563423833 2958658795540929422567875)
                ·
                  refine ⟨4437988193311394133851813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2958658795540929422567875 4437988193311394133851813)
                  ·
                    refine ⟨832122786245886400097215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4437988193311394133851813 832122786245886400097215)
                    ·
                      rfl

theorem cell22_2430830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_2430830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2430830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2430830 prefixEnd_2430830 := by exact prefixLift 2430830
  have htrace : WordTrace (prefixWord ++ tailWord_2430830) baseStart_2430830 baseEnd_2430830 := by
    simpa [prefixWord, tailWord_2430830, baseEnd_2430830] using wordTrace_append hprefix tailTrace_2430830
  have hstable : (prefixWord ++ tailWord_2430830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430830).length < 2 ^ (prefixWord ++ tailWord_2430830).sum := by decide
  have hdescent : baseEnd_2430830 < baseStart_2430830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430856 : List Nat := [2, 1, 3, 3, 3, 10]
def baseStart_2430856 : Nat := 118140960795 + 2430856 * 2 ^ 59
def prefixEnd_2430856 : Nat := 4983230072969 + 3 ^ 40 * 2430856 * 2
def baseEnd_2430856 : Nat := 10273230698484333320335

theorem tailTrace_2430856 : CollatzResearch.WordTrace tailWord_2430856 prefixEnd_2430856 10273230698484333320335 := by
  unfold tailWord_2430856
  simp only [CollatzResearch.WordTrace]
  refine ⟨44330301040715671998780211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59107068054287562665040281 44330301040715671998780211)
  ·
    refine ⟨66495451561073507998170317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44330301040715671998780211 66495451561073507998170317)
    ·
      refine ⟨24935794335402565499313869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66495451561073507998170317 24935794335402565499313869)
      ·
        refine ⟨9350922875775962062242701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24935794335402565499313869 9350922875775962062242701)
        ·
          refine ⟨3506596078415985773341013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9350922875775962062242701 3506596078415985773341013)
          ·
            refine ⟨10273230698484333320335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3506596078415985773341013 10273230698484333320335)
            ·
              rfl

theorem cell22_2430856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 10].length) (baseStart_2430856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2430856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2430856 prefixEnd_2430856 := by exact prefixLift 2430856
  have htrace : WordTrace (prefixWord ++ tailWord_2430856) baseStart_2430856 baseEnd_2430856 := by
    simpa [prefixWord, tailWord_2430856, baseEnd_2430856] using wordTrace_append hprefix tailTrace_2430856
  have hstable : (prefixWord ++ tailWord_2430856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430856).length < 2 ^ (prefixWord ++ tailWord_2430856).sum := by decide
  have hdescent : baseEnd_2430856 < baseStart_2430856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430862 : List Nat := [4, 1, 1, 5, 1, 1, 1, 4, 4]
def baseStart_2430862 : Nat := 118140960795 + 2430862 * 2 ^ 59
def prefixEnd_2430862 : Nat := 4983230072969 + 3 ^ 40 * 2430862 * 2
def baseEnd_2430862 : Nat := 277377913499949661099039

theorem tailTrace_2430862 : CollatzResearch.WordTrace tailWord_2430862 prefixEnd_2430862 277377913499949661099039 := by
  unfold tailWord_2430862
  simp only [CollatzResearch.WordTrace]
  refine ⟨11082602614926200877784855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59107213946273071348185893 11082602614926200877784855)
  ·
    refine ⟨16623903922389301316677283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11082602614926200877784855 16623903922389301316677283)
    ·
      refine ⟨24935855883583951975015925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16623903922389301316677283 24935855883583951975015925)
      ·
        refine ⟨2337736489085995497657743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24935855883583951975015925 2337736489085995497657743)
        ·
          refine ⟨3506604733628993246486615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2337736489085995497657743 3506604733628993246486615)
          ·
            refine ⟨5259907100443489869729923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3506604733628993246486615 5259907100443489869729923)
            ·
              refine ⟨7889860650665234804594885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5259907100443489869729923 7889860650665234804594885)
              ·
                refine ⟨1479348871999731525861541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7889860650665234804594885 1479348871999731525861541)
                ·
                  refine ⟨277377913499949661099039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1479348871999731525861541 277377913499949661099039)
                  ·
                    rfl

theorem cell22_2430862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_2430862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2430862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2430862 prefixEnd_2430862 := by exact prefixLift 2430862
  have htrace : WordTrace (prefixWord ++ tailWord_2430862) baseStart_2430862 baseEnd_2430862 := by
    simpa [prefixWord, tailWord_2430862, baseEnd_2430862] using wordTrace_append hprefix tailTrace_2430862
  have hstable : (prefixWord ++ tailWord_2430862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430862).length < 2 ^ (prefixWord ++ tailWord_2430862).sum := by decide
  have hdescent : baseEnd_2430862 < baseStart_2430862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430933 : List Nat := [1, 3, 2, 3, 2, 1, 2, 1, 2, 5]
def baseStart_2430933 : Nat := 118140960795 + 2430933 * 2 ^ 59
def prefixEnd_2430933 : Nat := 4983230072969 + 3 ^ 40 * 2430933 * 2
def baseEnd_2430933 : Nat := 832158045250828464771899

theorem tailTrace_2430933 : CollatzResearch.WordTrace tailWord_2430933 prefixEnd_2430933 832158045250828464771899 := by
  unfold tailWord_2430933
  simp only [CollatzResearch.WordTrace]
  refine ⟨88663410502152386148113453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59108940334768257432075635 88663410502152386148113453)
  ·
    refine ⟨33248778938307144805542545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88663410502152386148113453 33248778938307144805542545)
    ·
      refine ⟨24936584203730358604156909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33248778938307144805542545 24936584203730358604156909)
      ·
        refine ⟨9351219076398884476558841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24936584203730358604156909 9351219076398884476558841)
        ·
          refine ⟨7013414307299163357419131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9351219076398884476558841 7013414307299163357419131)
          ·
            refine ⟨10520121460948745036128697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7013414307299163357419131 10520121460948745036128697)
            ·
              refine ⟨7890091095711558777096523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10520121460948745036128697 7890091095711558777096523)
              ·
                refine ⟨11835136643567338165644785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7890091095711558777096523 11835136643567338165644785)
                ·
                  refine ⟨8876352482675503624233589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11835136643567338165644785 8876352482675503624233589)
                  ·
                    refine ⟨832158045250828464771899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8876352482675503624233589 832158045250828464771899)
                    ·
                      rfl

theorem cell22_2430933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_2430933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2430933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2430933 prefixEnd_2430933 := by exact prefixLift 2430933
  have htrace : WordTrace (prefixWord ++ tailWord_2430933) baseStart_2430933 baseEnd_2430933 := by
    simpa [prefixWord, tailWord_2430933, baseEnd_2430933] using wordTrace_append hprefix tailTrace_2430933
  have hstable : (prefixWord ++ tailWord_2430933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430933).length < 2 ^ (prefixWord ++ tailWord_2430933).sum := by decide
  have hdescent : baseEnd_2430933 < baseStart_2430933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430976 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 3, 6]
def baseStart_2430976 : Nat := 118140960795 + 2430976 * 2 ^ 59
def prefixEnd_2430976 : Nat := 4983230072969 + 3 ^ 40 * 2430976 * 2
def baseEnd_2430976 : Nat := 832172765029590685946767

theorem tailTrace_2430976 : CollatzResearch.WordTrace tailWord_2430976 prefixEnd_2430976 832172765029590685946767 := by
  unfold tailWord_2430976
  simp only [CollatzResearch.WordTrace]
  refine ⟨44332489420498302245964391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59109985893997736327952521 44332489420498302245964391)
  ·
    refine ⟨66498734130747453368946587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44332489420498302245964391 66498734130747453368946587)
    ·
      refine ⟨99748101196121180053419881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66498734130747453368946587 99748101196121180053419881)
      ·
        refine ⟨74811075897090885040064911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99748101196121180053419881 74811075897090885040064911)
        ·
          refine ⟨112216613845636327560097367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74811075897090885040064911 112216613845636327560097367)
          ·
            refine ⟨168324920768454491340146051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112216613845636327560097367 168324920768454491340146051)
            ·
              refine ⟨252487381152681737010219077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168324920768454491340146051 252487381152681737010219077)
              ·
                refine ⟨47341383966127825689416077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 252487381152681737010219077 47341383966127825689416077)
                ·
                  refine ⟨17753018987297934633531029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47341383966127825689416077 17753018987297934633531029)
                  ·
                    refine ⟨832172765029590685946767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17753018987297934633531029 832172765029590685946767)
                    ·
                      rfl

theorem cell22_2430976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 3, 6].length) (baseStart_2430976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2430976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2430976 prefixEnd_2430976 := by exact prefixLift 2430976
  have htrace : WordTrace (prefixWord ++ tailWord_2430976) baseStart_2430976 baseEnd_2430976 := by
    simpa [prefixWord, tailWord_2430976, baseEnd_2430976] using wordTrace_append hprefix tailTrace_2430976
  have hstable : (prefixWord ++ tailWord_2430976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430976).length < 2 ^ (prefixWord ++ tailWord_2430976).sum := by decide
  have hdescent : baseEnd_2430976 < baseStart_2430976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430999 : List Nat := [1, 1, 3, 5, 3, 1, 1, 2, 1, 4]
def baseStart_2430999 : Nat := 118140960795 + 2430999 * 2 ^ 59
def prefixEnd_2430999 : Nat := 4983230072969 + 3 ^ 40 * 2430999 * 2
def baseEnd_2430999 : Nat := 832180638399626292621697

theorem tailTrace_2430999 : CollatzResearch.WordTrace tailWord_2430999 prefixEnd_2430999 832180638399626292621697 := by
  unfold tailWord_2430999
  simp only [CollatzResearch.WordTrace]
  refine ⟨88665817719913279420016051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59110545146608852946677367 88665817719913279420016051)
  ·
    refine ⟨132998726579869919130024077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88665817719913279420016051 132998726579869919130024077)
    ·
      refine ⟨49874522467451219673759029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132998726579869919130024077 49874522467451219673759029)
      ·
        refine ⟨4675736481323551844414909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49874522467451219673759029 4675736481323551844414909)
        ·
          refine ⟨1753401180496331941655591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4675736481323551844414909 1753401180496331941655591)
          ·
            refine ⟨2630101770744497912483387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1753401180496331941655591 2630101770744497912483387)
            ·
              refine ⟨3945152656116746868725081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2630101770744497912483387 3945152656116746868725081)
              ·
                refine ⟨2958864492087560151543811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3945152656116746868725081 2958864492087560151543811)
                ·
                  refine ⟨4438296738131340227315717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2958864492087560151543811 4438296738131340227315717)
                  ·
                    refine ⟨832180638399626292621697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4438296738131340227315717 832180638399626292621697)
                    ·
                      rfl

theorem cell22_2430999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 1, 4].length) (baseStart_2430999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2430999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2430999 prefixEnd_2430999 := by exact prefixLift 2430999
  have htrace : WordTrace (prefixWord ++ tailWord_2430999) baseStart_2430999 baseEnd_2430999 := by
    simpa [prefixWord, tailWord_2430999, baseEnd_2430999] using wordTrace_append hprefix tailTrace_2430999
  have hstable : (prefixWord ++ tailWord_2430999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430999).length < 2 ^ (prefixWord ++ tailWord_2430999).sum := by decide
  have hdescent : baseEnd_2430999 < baseStart_2430999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431010 : List Nat := [3, 3, 1, 1, 1, 2, 4, 1, 2, 4]
def baseStart_2431010 : Nat := 118140960795 + 2431010 * 2 ^ 59
def prefixEnd_2431010 : Nat := 4983230072969 + 3 ^ 40 * 2431010 * 2
def baseEnd_2431010 : Nat := 832184403924425930596663

theorem tailTrace_2431010 : CollatzResearch.WordTrace tailWord_2431010 prefixEnd_2431010 832184403924425930596663 := by
  unfold tailWord_2431010
  simp only [CollatzResearch.WordTrace]
  refine ⟨22166554730718357074666621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59110812615248952199110989 22166554730718357074666621)
  ·
    refine ⟨8312458024019383902999983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22166554730718357074666621 8312458024019383902999983)
    ·
      refine ⟨12468687036029075854499975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8312458024019383902999983 12468687036029075854499975)
      ·
        refine ⟨18703030554043613781749963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12468687036029075854499975 18703030554043613781749963)
        ·
          refine ⟨28054545831065420672624945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18703030554043613781749963 28054545831065420672624945)
          ·
            refine ⟨21040909373299065504468709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28054545831065420672624945 21040909373299065504468709)
            ·
              refine ⟨3945170507493574782087883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21040909373299065504468709 3945170507493574782087883)
              ·
                refine ⟨5917755761240362173131825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3945170507493574782087883 5917755761240362173131825)
                ·
                  refine ⟨4438316820930271629848869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5917755761240362173131825 4438316820930271629848869)
                  ·
                    refine ⟨832184403924425930596663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4438316820930271629848869 832184403924425930596663)
                    ·
                      rfl

theorem cell22_2431010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_2431010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431010 prefixEnd_2431010 := by exact prefixLift 2431010
  have htrace : WordTrace (prefixWord ++ tailWord_2431010) baseStart_2431010 baseEnd_2431010 := by
    simpa [prefixWord, tailWord_2431010, baseEnd_2431010] using wordTrace_append hprefix tailTrace_2431010
  have hstable : (prefixWord ++ tailWord_2431010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431010).length < 2 ^ (prefixWord ++ tailWord_2431010).sum := by decide
  have hdescent : baseEnd_2431010 < baseStart_2431010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431023 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 7, 3]
def baseStart_2431023 : Nat := 118140960795 + 2431023 * 2 ^ 59
def prefixEnd_2431023 : Nat := 4983230072969 + 3 ^ 40 * 2431023 * 2
def baseEnd_2431023 : Nat := 832188854090098230021623

theorem tailTrace_2431023 : CollatzResearch.WordTrace tailWord_2431023 prefixEnd_2431023 832188854090098230021623 := by
  unfold tailWord_2431023
  simp only [CollatzResearch.WordTrace]
  refine ⟨88666693071826331518889723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59111128714550887679259815 88666693071826331518889723)
  ·
    refine ⟨133000039607739497278334585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88666693071826331518889723 133000039607739497278334585)
    ·
      refine ⟨99750029705804622958750939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133000039607739497278334585 99750029705804622958750939)
      ·
        refine ⟨149625044558706934438126409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99750029705804622958750939 149625044558706934438126409)
        ·
          refine ⟨112218783419030200828594807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149625044558706934438126409 112218783419030200828594807)
          ·
            refine ⟨168328175128545301242892211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112218783419030200828594807 168328175128545301242892211)
            ·
              refine ⟨252492262692817951864338317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168328175128545301242892211 252492262692817951864338317)
              ·
                refine ⟨94684598509806731949126869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 252492262692817951864338317 94684598509806731949126869)
                ·
                  refine ⟨2219170277573595280057661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 94684598509806731949126869 2219170277573595280057661)
                  ·
                    refine ⟨832188854090098230021623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2219170277573595280057661 832188854090098230021623)
                    ·
                      rfl

theorem cell22_2431023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 7, 3].length) (baseStart_2431023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431023 prefixEnd_2431023 := by exact prefixLift 2431023
  have htrace : WordTrace (prefixWord ++ tailWord_2431023) baseStart_2431023 baseEnd_2431023 := by
    simpa [prefixWord, tailWord_2431023, baseEnd_2431023] using wordTrace_append hprefix tailTrace_2431023
  have hstable : (prefixWord ++ tailWord_2431023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431023).length < 2 ^ (prefixWord ++ tailWord_2431023).sum := by decide
  have hdescent : baseEnd_2431023 < baseStart_2431023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431164 : List Nat := [2, 2, 2, 3, 3, 1, 1, 3, 2, 3]
def baseStart_2431164 : Nat := 118140960795 + 2431164 * 2 ^ 59
def prefixEnd_2431164 : Nat := 4983230072969 + 3 ^ 40 * 2431164 * 2
def baseEnd_2431164 : Nat := 832237121271620862246191

theorem tailTrace_2431164 : CollatzResearch.WordTrace tailWord_2431164 prefixEnd_2431164 832237121271620862246191 := by
  unfold tailWord_2431164
  simp only [CollatzResearch.WordTrace]
  refine ⟨44335917882157756299886273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59114557176210341733181697 44335917882157756299886273)
  ·
    refine ⟨33251938411618317224914705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44335917882157756299886273 33251938411618317224914705)
    ·
      refine ⟨24938953808713737918686029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33251938411618317224914705 24938953808713737918686029)
      ·
        refine ⟨9352107678267651719507261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24938953808713737918686029 9352107678267651719507261)
        ·
          refine ⟨3507040379350369394815223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9352107678267651719507261 3507040379350369394815223)
          ·
            refine ⟨5260560569025554092222835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3507040379350369394815223 5260560569025554092222835)
            ·
              refine ⟨7890840853538331138334253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5260560569025554092222835 7890840853538331138334253)
              ·
                refine ⟨2959065320076874176875345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7890840853538331138334253 2959065320076874176875345)
                ·
                  refine ⟨2219298990057655632656509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2959065320076874176875345 2219298990057655632656509)
                  ·
                    refine ⟨832237121271620862246191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2219298990057655632656509 832237121271620862246191)
                    ·
                      rfl

theorem cell22_2431164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_2431164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431164 prefixEnd_2431164 := by exact prefixLift 2431164
  have htrace : WordTrace (prefixWord ++ tailWord_2431164) baseStart_2431164 baseEnd_2431164 := by
    simpa [prefixWord, tailWord_2431164, baseEnd_2431164] using wordTrace_append hprefix tailTrace_2431164
  have hstable : (prefixWord ++ tailWord_2431164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431164).length < 2 ^ (prefixWord ++ tailWord_2431164).sum := by decide
  have hdescent : baseEnd_2431164 < baseStart_2431164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431222 : List Nat := [5, 1, 1, 1, 1, 1, 4, 3, 5]
def baseStart_2431222 : Nat := 118140960795 + 2431222 * 2 ^ 59
def prefixEnd_2431222 : Nat := 4983230072969 + 3 ^ 40 * 2431222 * 2
def baseEnd_2431222 : Nat := 277418991952309348098671

theorem tailTrace_2431222 : CollatzResearch.WordTrace tailWord_2431222 prefixEnd_2431222 277418991952309348098671 := by
  unfold tailWord_2431222
  simp only [CollatzResearch.WordTrace]
  refine ⟨5542121949881586781586495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59115967465403592336922613 5542121949881586781586495)
  ·
    refine ⟨8313182924822380172379743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5542121949881586781586495 8313182924822380172379743)
    ·
      refine ⟨12469774387233570258569615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8313182924822380172379743 12469774387233570258569615)
      ·
        refine ⟨18704661580850355387854423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12469774387233570258569615 18704661580850355387854423)
        ·
          refine ⟨28056992371275533081781635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18704661580850355387854423 28056992371275533081781635)
          ·
            refine ⟨42085488556913299622672453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28056992371275533081781635 42085488556913299622672453)
            ·
              refine ⟨7891029104421243679251085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42085488556913299622672453 7891029104421243679251085)
              ·
                refine ⟨2959135914157966379719157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7891029104421243679251085 2959135914157966379719157)
                ·
                  refine ⟨277418991952309348098671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2959135914157966379719157 277418991952309348098671)
                  ·
                    rfl

theorem cell22_2431222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_2431222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431222 prefixEnd_2431222 := by exact prefixLift 2431222
  have htrace : WordTrace (prefixWord ++ tailWord_2431222) baseStart_2431222 baseEnd_2431222 := by
    simpa [prefixWord, tailWord_2431222, baseEnd_2431222] using wordTrace_append hprefix tailTrace_2431222
  have hstable : (prefixWord ++ tailWord_2431222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431222).length < 2 ^ (prefixWord ++ tailWord_2431222).sum := by decide
  have hdescent : baseEnd_2431222 < baseStart_2431222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431235 : List Nat := [1, 1, 1, 3, 2, 3, 1, 3, 3, 4]
def baseStart_2431235 : Nat := 118140960795 + 2431235 * 2 ^ 59
def prefixEnd_2431235 : Nat := 4983230072969 + 3 ^ 40 * 2431235 * 2
def baseEnd_2431235 : Nat := 832261426022600343720973

theorem tailTrace_2431235 : CollatzResearch.WordTrace tailWord_2431235 prefixEnd_2431235 832261426022600343720973 := by
  unfold tailWord_2431235
  simp only [CollatzResearch.WordTrace]
  refine ⟨88674425347058291725607159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59116283564705527817071439 88674425347058291725607159)
  ·
    refine ⟨133011638020587437588410739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88674425347058291725607159 133011638020587437588410739)
    ·
      refine ⟨199517457030881156382616109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133011638020587437588410739 199517457030881156382616109)
      ·
        refine ⟨74819046386580433643481041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199517457030881156382616109 74819046386580433643481041)
        ·
          refine ⟨56114284789935325232610781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74819046386580433643481041 56114284789935325232610781)
          ·
            refine ⟨21042856796225746962229043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56114284789935325232610781 21042856796225746962229043)
            ·
              refine ⟨31564285194338620443343565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21042856796225746962229043 31564285194338620443343565)
              ·
                refine ⟨11836606947876982666253837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31564285194338620443343565 11836606947876982666253837)
                ·
                  refine ⟨4438727605453868499845189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11836606947876982666253837 4438727605453868499845189)
                  ·
                    refine ⟨832261426022600343720973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4438727605453868499845189 832261426022600343720973)
                    ·
                      rfl

theorem cell22_2431235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 4].length) (baseStart_2431235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431235 prefixEnd_2431235 := by exact prefixLift 2431235
  have htrace : WordTrace (prefixWord ++ tailWord_2431235) baseStart_2431235 baseEnd_2431235 := by
    simpa [prefixWord, tailWord_2431235, baseEnd_2431235] using wordTrace_append hprefix tailTrace_2431235
  have hstable : (prefixWord ++ tailWord_2431235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431235).length < 2 ^ (prefixWord ++ tailWord_2431235).sum := by decide
  have hdescent : baseEnd_2431235 < baseStart_2431235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431265 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 3, 5]
def baseStart_2431265 : Nat := 118140960795 + 2431265 * 2 ^ 59
def prefixEnd_2431265 : Nat := 4983230072969 + 3 ^ 40 * 2431265 * 2
def baseEnd_2431265 : Nat := 832271695635690265470881

theorem tailTrace_2431265 : CollatzResearch.WordTrace tailWord_2431265 prefixEnd_2431265 832271695635690265470881 := by
  unfold tailWord_2431265
  simp only [CollatzResearch.WordTrace]
  refine ⟨88675519536949606849199249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59117013024633071232799499 88675519536949606849199249)
  ·
    refine ⟨66506639652712205136899437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88675519536949606849199249 66506639652712205136899437)
    ·
      refine ⟨24939989869767076926337289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66506639652712205136899437 24939989869767076926337289)
      ·
        refine ⟨18704992402325307694752967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24939989869767076926337289 18704992402325307694752967)
        ·
          refine ⟨28057488603487961542129451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18704992402325307694752967 28057488603487961542129451)
          ·
            refine ⟨42086232905231942313194177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28057488603487961542129451 42086232905231942313194177)
            ·
              refine ⟨31564674678923956734895633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42086232905231942313194177 31564674678923956734895633)
              ·
                refine ⟨23673506009192967551171725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31564674678923956734895633 23673506009192967551171725)
                ·
                  refine ⟨8877564753447362831689397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23673506009192967551171725 8877564753447362831689397)
                  ·
                    refine ⟨832271695635690265470881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8877564753447362831689397 832271695635690265470881)
                    ·
                      rfl

theorem cell22_2431265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_2431265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431265 prefixEnd_2431265 := by exact prefixLift 2431265
  have htrace : WordTrace (prefixWord ++ tailWord_2431265) baseStart_2431265 baseEnd_2431265 := by
    simpa [prefixWord, tailWord_2431265, baseEnd_2431265] using wordTrace_append hprefix tailTrace_2431265
  have hstable : (prefixWord ++ tailWord_2431265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431265).length < 2 ^ (prefixWord ++ tailWord_2431265).sum := by decide
  have hdescent : baseEnd_2431265 < baseStart_2431265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431267 : List Nat := [1, 1, 1, 4, 2, 2, 1, 6, 4]
def baseStart_2431267 : Nat := 118140960795 + 2431267 * 2 ^ 59
def prefixEnd_2431267 : Nat := 4983230072969 + 3 ^ 40 * 2431267 * 2
def baseEnd_2431267 : Nat := 277424126758854308973625

theorem tailTrace_2431267 : CollatzResearch.WordTrace tailWord_2431267 prefixEnd_2431267 277424126758854308973625 := by
  unfold tailWord_2431267
  simp only [CollatzResearch.WordTrace]
  refine ⟨88675592482942361190772055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59117061655294907460514703 88675592482942361190772055)
  ·
    refine ⟨133013388724413541786158083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88675592482942361190772055 133013388724413541786158083)
    ·
      refine ⟨199520083086620312679237125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133013388724413541786158083 199520083086620312679237125)
      ·
        refine ⟨37410015578741308627356961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 199520083086620312679237125 37410015578741308627356961)
        ·
          refine ⟨28057511684055981470517721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37410015578741308627356961 28057511684055981470517721)
          ·
            refine ⟨21043133763041986102888291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28057511684055981470517721 21043133763041986102888291)
            ·
              refine ⟨31564700644562979154332437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21043133763041986102888291 31564700644562979154332437)
              ·
                refine ⟨1479595342713889647859333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31564700644562979154332437 1479595342713889647859333)
                ·
                  refine ⟨277424126758854308973625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1479595342713889647859333 277424126758854308973625)
                  ·
                    rfl

theorem cell22_2431267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 6, 4].length) (baseStart_2431267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431267 prefixEnd_2431267 := by exact prefixLift 2431267
  have htrace : WordTrace (prefixWord ++ tailWord_2431267) baseStart_2431267 baseEnd_2431267 := by
    simpa [prefixWord, tailWord_2431267, baseEnd_2431267] using wordTrace_append hprefix tailTrace_2431267
  have hstable : (prefixWord ++ tailWord_2431267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431267).length < 2 ^ (prefixWord ++ tailWord_2431267).sum := by decide
  have hdescent : baseEnd_2431267 < baseStart_2431267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431280 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 6, 4]
def baseStart_2431280 : Nat := 118140960795 + 2431280 * 2 ^ 59
def prefixEnd_2431280 : Nat := 4983230072969 + 3 ^ 40 * 2431280 * 2
def baseEnd_2431280 : Nat := 832276830442235226345835

theorem tailTrace_2431280 : CollatzResearch.WordTrace tailWord_2431280 prefixEnd_2431280 832276830442235226345835 := by
  unfold tailWord_2431280
  simp only [CollatzResearch.WordTrace]
  refine ⟨44338033315947632205497647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59117377754596842940663529 44338033315947632205497647)
  ·
    refine ⟨66507049973921448308246471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44338033315947632205497647 66507049973921448308246471)
    ·
      refine ⟨99760574960882172462369707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66507049973921448308246471 99760574960882172462369707)
      ·
        refine ⟨149640862441323258693554561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99760574960882172462369707 149640862441323258693554561)
        ·
          refine ⟨112230646830992444020165921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149640862441323258693554561 112230646830992444020165921)
          ·
            refine ⟨84172985123244333015124441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112230646830992444020165921 84172985123244333015124441)
            ·
              refine ⟨63129738842433249761343331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84172985123244333015124441 63129738842433249761343331)
              ·
                refine ⟨94694608263649874642014997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63129738842433249761343331 94694608263649874642014997)
                ·
                  refine ⟨4438809762358587873844453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 94694608263649874642014997 4438809762358587873844453)
                  ·
                    refine ⟨832276830442235226345835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4438809762358587873844453 832276830442235226345835)
                    ·
                      rfl

theorem cell22_2431280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 6, 4].length) (baseStart_2431280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431280 prefixEnd_2431280 := by exact prefixLift 2431280
  have htrace : WordTrace (prefixWord ++ tailWord_2431280) baseStart_2431280 baseEnd_2431280 := by
    simpa [prefixWord, tailWord_2431280, baseEnd_2431280] using wordTrace_append hprefix tailTrace_2431280
  have hstable : (prefixWord ++ tailWord_2431280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431280).length < 2 ^ (prefixWord ++ tailWord_2431280).sum := by decide
  have hdescent : baseEnd_2431280 < baseStart_2431280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431295 : List Nat := [1, 1, 2, 2, 4, 1, 3, 8]
def baseStart_2431295 : Nat := 118140960795 + 2431295 * 2 ^ 59
def prefixEnd_2431295 : Nat := 4983230072969 + 3 ^ 40 * 2431295 * 2
def baseEnd_2431295 : Nat := 92475773916531131913421

theorem tailTrace_2431295 : CollatzResearch.WordTrace tailWord_2431295 prefixEnd_2431295 92475773916531131913421 := by
  unfold tailWord_2431295
  simp only [CollatzResearch.WordTrace]
  refine ⟨88676613726840921972791339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59117742484560614648527559 88676613726840921972791339)
  ·
    refine ⟨133014920590261382959187009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88676613726840921972791339 133014920590261382959187009)
    ·
      refine ⟨99761190442696037219390257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133014920590261382959187009 99761190442696037219390257)
      ·
        refine ⟨74820892832022027914542693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99761190442696037219390257 74820892832022027914542693)
        ·
          refine ⟨14028917406004130233976755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74820892832022027914542693 14028917406004130233976755)
          ·
            refine ⟨21043376109006195350965133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14028917406004130233976755 21043376109006195350965133)
            ·
              refine ⟨7891266040877323256611925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21043376109006195350965133 7891266040877323256611925)
              ·
                refine ⟨92475773916531131913421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7891266040877323256611925 92475773916531131913421)
                ·
                  rfl

theorem cell22_2431295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 8].length) (baseStart_2431295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431295 prefixEnd_2431295 := by exact prefixLift 2431295
  have htrace : WordTrace (prefixWord ++ tailWord_2431295) baseStart_2431295 baseEnd_2431295 := by
    simpa [prefixWord, tailWord_2431295, baseEnd_2431295] using wordTrace_append hprefix tailTrace_2431295
  have hstable : (prefixWord ++ tailWord_2431295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431295).length < 2 ^ (prefixWord ++ tailWord_2431295).sum := by decide
  have hdescent : baseEnd_2431295 < baseStart_2431295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431374 : List Nat := [4, 1, 1, 4, 1, 1, 1, 4, 5]
def baseStart_2431374 : Nat := 118140960795 + 2431374 * 2 ^ 59
def prefixEnd_2431374 : Nat := 4983230072969 + 3 ^ 40 * 2431374 * 2
def baseEnd_2431374 : Nat := 277436336187750104831849

theorem tailTrace_2431374 : CollatzResearch.WordTrace tailWord_2431374 prefixEnd_2431374 277436336187750104831849 := by
  unfold tailWord_2431374
  simp only [CollatzResearch.WordTrace]
  refine ⟨11084936886694339808114647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59119663395703145643278117 11084936886694339808114647)
  ·
    refine ⟨16627405330041509712171971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11084936886694339808114647 16627405330041509712171971)
    ·
      refine ⟨24941107995062264568257957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16627405330041509712171971 24941107995062264568257957)
      ·
        refine ⟨4676457749074174606548367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24941107995062264568257957 4676457749074174606548367)
        ·
          refine ⟨7014686623611261909822551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4676457749074174606548367 7014686623611261909822551)
          ·
            refine ⟨10522029935416892864733827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7014686623611261909822551 10522029935416892864733827)
            ·
              refine ⟨15783044903125339297100741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10522029935416892864733827 15783044903125339297100741)
              ·
                refine ⟨2959320919336001118206389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15783044903125339297100741 2959320919336001118206389)
                ·
                  refine ⟨277436336187750104831849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2959320919336001118206389 277436336187750104831849)
                  ·
                    rfl

theorem cell22_2431374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_2431374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431374 prefixEnd_2431374 := by exact prefixLift 2431374
  have htrace : WordTrace (prefixWord ++ tailWord_2431374) baseStart_2431374 baseEnd_2431374 := by
    simpa [prefixWord, tailWord_2431374, baseEnd_2431374] using wordTrace_append hprefix tailTrace_2431374
  have hstable : (prefixWord ++ tailWord_2431374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431374).length < 2 ^ (prefixWord ++ tailWord_2431374).sum := by decide
  have hdescent : baseEnd_2431374 < baseStart_2431374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431389 : List Nat := [1, 4, 2, 1, 4, 1, 1, 1, 2, 5]
def baseStart_2431389 : Nat := 118140960795 + 2431389 * 2 ^ 59
def prefixEnd_2431389 : Nat := 4983230072969 + 3 ^ 40 * 2431389 * 2
def baseEnd_2431389 : Nat := 832314143369795275370501

theorem tailTrace_2431389 : CollatzResearch.WordTrace tailWord_2431389 prefixEnd_2431389 832314143369795275370501 := by
  unfold tailWord_2431389
  simp only [CollatzResearch.WordTrace]
  refine ⟨88680042188500376026713221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59120028125666917351142147 88680042188500376026713221)
  ·
    refine ⟨16627507910343820505008729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88680042188500376026713221 16627507910343820505008729)
    ·
      refine ⟨12470630932757865378756547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16627507910343820505008729 12470630932757865378756547)
      ·
        refine ⟨18705946399136798068134821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12470630932757865378756547 18705946399136798068134821)
        ·
          refine ⟨3507364949838149637775279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18705946399136798068134821 3507364949838149637775279)
          ·
            refine ⟨5261047424757224456662919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3507364949838149637775279 5261047424757224456662919)
            ·
              refine ⟨7891571137135836684994379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5261047424757224456662919 7891571137135836684994379)
              ·
                refine ⟨11837356705703755027491569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7891571137135836684994379 11837356705703755027491569)
                ·
                  refine ⟨8878017529277816270618677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11837356705703755027491569 8878017529277816270618677)
                  ·
                    refine ⟨832314143369795275370501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8878017529277816270618677 832314143369795275370501)
                    ·
                      rfl

theorem cell22_2431389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_2431389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431389 prefixEnd_2431389 := by exact prefixLift 2431389
  have htrace : WordTrace (prefixWord ++ tailWord_2431389) baseStart_2431389 baseEnd_2431389 := by
    simpa [prefixWord, tailWord_2431389, baseEnd_2431389] using wordTrace_append hprefix tailTrace_2431389
  have hstable : (prefixWord ++ tailWord_2431389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431389).length < 2 ^ (prefixWord ++ tailWord_2431389).sum := by decide
  have hdescent : baseEnd_2431389 < baseStart_2431389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431412 : List Nat := [2, 5, 2, 2, 1, 1, 2, 3, 1, 3]
def baseStart_2431412 : Nat := 118140960795 + 2431412 * 2 ^ 59
def prefixEnd_2431412 : Nat := 4983230072969 + 3 ^ 40 * 2431412 * 2
def baseEnd_2431412 : Nat := 832322016739830882045431

theorem tailTrace_2431412 : CollatzResearch.WordTrace tailWord_2431412 prefixEnd_2431412 832322016739830882045431 := by
  unfold tailWord_2431412
  simp only [CollatzResearch.WordTrace]
  refine ⟨44340440533708525477400245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59120587378278033969866993 44340440533708525477400245)
  ·
    refine ⟨4156916300035174263506273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44340440533708525477400245 4156916300035174263506273)
    ·
      refine ⟨3117687225026380697629705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4156916300035174263506273 3117687225026380697629705)
      ·
        refine ⟨2338265418769785523222279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3117687225026380697629705 2338265418769785523222279)
        ·
          refine ⟨3507398128154678284833419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2338265418769785523222279 3507398128154678284833419)
          ·
            refine ⟨5261097192232017427250129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3507398128154678284833419 5261097192232017427250129)
            ·
              refine ⟨3945822894174013070437597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5261097192232017427250129 3945822894174013070437597)
              ·
                refine ⟨1479683585315254901414099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3945822894174013070437597 1479683585315254901414099)
                ·
                  refine ⟨2219525377972882352121149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1479683585315254901414099 2219525377972882352121149)
                  ·
                    refine ⟨832322016739830882045431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2219525377972882352121149 832322016739830882045431)
                    ·
                      rfl

theorem cell22_2431412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_2431412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431412 prefixEnd_2431412 := by exact prefixLift 2431412
  have htrace : WordTrace (prefixWord ++ tailWord_2431412) baseStart_2431412 baseEnd_2431412 := by
    simpa [prefixWord, tailWord_2431412, baseEnd_2431412] using wordTrace_append hprefix tailTrace_2431412
  have hstable : (prefixWord ++ tailWord_2431412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431412).length < 2 ^ (prefixWord ++ tailWord_2431412).sum := by decide
  have hdescent : baseEnd_2431412 < baseStart_2431412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431421 : List Nat := [1, 4, 1, 2, 2, 2, 4, 1, 1, 4]
def baseStart_2431421 : Nat := 118140960795 + 2431421 * 2 ^ 59
def prefixEnd_2431421 : Nat := 4983230072969 + 3 ^ 40 * 2431421 * 2
def baseEnd_2431421 : Nat := 832325097623757858570403

theorem tailTrace_2431421 : CollatzResearch.WordTrace tailWord_2431421 prefixEnd_2431421 832325097623757858570403 := by
  unfold tailWord_2431421
  simp only [CollatzResearch.WordTrace]
  refine ⟨88681209324384445491878117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59120806216256296994585411 88681209324384445491878117)
  ·
    refine ⟨16627726748322083529727147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88681209324384445491878117 16627726748322083529727147)
    ·
      refine ⟨24941590122483125294590721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16627726748322083529727147 24941590122483125294590721)
      ·
        refine ⟨18706192591862343970943041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24941590122483125294590721 18706192591862343970943041)
        ·
          refine ⟨14029644443896757978207281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18706192591862343970943041 14029644443896757978207281)
          ·
            refine ⟨10522233332922568483655461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14029644443896757978207281 10522233332922568483655461)
            ·
              refine ⟨1972918749922981590685399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10522233332922568483655461 1972918749922981590685399)
              ·
                refine ⟨2959378124884472386028099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1972918749922981590685399 2959378124884472386028099)
                ·
                  refine ⟨4439067187326708579042149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2959378124884472386028099 4439067187326708579042149)
                  ·
                    refine ⟨832325097623757858570403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4439067187326708579042149 832325097623757858570403)
                    ·
                      rfl

theorem cell22_2431421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_2431421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431421 prefixEnd_2431421 := by exact prefixLift 2431421
  have htrace : WordTrace (prefixWord ++ tailWord_2431421) baseStart_2431421 baseEnd_2431421 := by
    simpa [prefixWord, tailWord_2431421, baseEnd_2431421] using wordTrace_append hprefix tailTrace_2431421
  have hstable : (prefixWord ++ tailWord_2431421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431421).length < 2 ^ (prefixWord ++ tailWord_2431421).sum := by decide
  have hdescent : baseEnd_2431421 < baseStart_2431421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431425 : List Nat := [1, 2, 7, 1, 1, 2, 1, 2, 5]
def baseStart_2431425 : Nat := 118140960795 + 2431425 * 2 ^ 59
def prefixEnd_2431425 : Nat := 4983230072969 + 3 ^ 40 * 2431425 * 2
def baseEnd_2431425 : Nat := 277442155635167727156797

theorem tailTrace_2431425 : CollatzResearch.WordTrace tailWord_2431425 prefixEnd_2431425 277442155635167727156797 := by
  unfold tailWord_2431425
  simp only [CollatzResearch.WordTrace]
  refine ⟨88681355216369954175023729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59120903477579969450015819 88681355216369954175023729)
  ·
    refine ⟨66511016412277465631267797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88681355216369954175023729 66511016412277465631267797)
    ·
      refine ⟨1558851947162753100732839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 66511016412277465631267797 1558851947162753100732839)
      ·
        refine ⟨2338277920744129651099259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1558851947162753100732839 2338277920744129651099259)
        ·
          refine ⟨3507416881116194476648889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2338277920744129651099259 3507416881116194476648889)
          ·
            refine ⟨2630562660837145857486667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3507416881116194476648889 2630562660837145857486667)
            ·
              refine ⟨3945843991255718786230001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2630562660837145857486667 3945843991255718786230001)
              ·
                refine ⟨2959382993441789089672501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3945843991255718786230001 2959382993441789089672501)
                ·
                  refine ⟨277442155635167727156797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2959382993441789089672501 277442155635167727156797)
                  ·
                    rfl

theorem cell22_2431425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 5].length) (baseStart_2431425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431425 prefixEnd_2431425 := by exact prefixLift 2431425
  have htrace : WordTrace (prefixWord ++ tailWord_2431425) baseStart_2431425 baseEnd_2431425 := by
    simpa [prefixWord, tailWord_2431425, baseEnd_2431425] using wordTrace_append hprefix tailTrace_2431425
  have hstable : (prefixWord ++ tailWord_2431425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431425).length < 2 ^ (prefixWord ++ tailWord_2431425).sum := by decide
  have hdescent : baseEnd_2431425 < baseStart_2431425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431434 : List Nat := [3, 1, 2, 1, 2, 2, 3, 1, 4, 3]
def baseStart_2431434 : Nat := 118140960795 + 2431434 * 2 ^ 59
def prefixEnd_2431434 : Nat := 4983230072969 + 3 ^ 40 * 2431434 * 2
def baseEnd_2431434 : Nat := 832329547789430157995363

theorem tailTrace_2431434 : CollatzResearch.WordTrace tailWord_2431434 prefixEnd_2431434 832329547789430157995363 := by
  unfold tailWord_2431434
  simp only [CollatzResearch.WordTrace]
  refine ⟨22170420868334337178025339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59121122315558232474734237 22170420868334337178025339)
  ·
    refine ⟨33255631302501505767038009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22170420868334337178025339 33255631302501505767038009)
    ·
      refine ⟨24941723476876129325278507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33255631302501505767038009 24941723476876129325278507)
      ·
        refine ⟨37412585215314193987917761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24941723476876129325278507 37412585215314193987917761)
        ·
          refine ⟨28059438911485645490938321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37412585215314193987917761 28059438911485645490938321)
          ·
            refine ⟨21044579183614234118203741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28059438911485645490938321 21044579183614234118203741)
            ·
              refine ⟨7891717193855337794326403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21044579183614234118203741 7891717193855337794326403)
              ·
                refine ⟨11837575790783006691489605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7891717193855337794326403 11837575790783006691489605)
                ·
                  refine ⟨2219545460771813754654301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11837575790783006691489605 2219545460771813754654301)
                  ·
                    refine ⟨832329547789430157995363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2219545460771813754654301 832329547789430157995363)
                    ·
                      rfl

theorem cell22_2431434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_2431434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431434 prefixEnd_2431434 := by exact prefixLift 2431434
  have htrace : WordTrace (prefixWord ++ tailWord_2431434) baseStart_2431434 baseEnd_2431434 := by
    simpa [prefixWord, tailWord_2431434, baseEnd_2431434] using wordTrace_append hprefix tailTrace_2431434
  have hstable : (prefixWord ++ tailWord_2431434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431434).length < 2 ^ (prefixWord ++ tailWord_2431434).sum := by decide
  have hdescent : baseEnd_2431434 < baseStart_2431434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431464 : List Nat := [2, 1, 4, 1, 1, 3, 4, 6]
def baseStart_2431464 : Nat := 118140960795 + 2431464 * 2 ^ 59
def prefixEnd_2431464 : Nat := 4983230072969 + 3 ^ 40 * 2431464 * 2
def baseEnd_2431464 : Nat := 92482201933613342193919

theorem tailTrace_2431464 : CollatzResearch.WordTrace tailWord_2431464 prefixEnd_2431464 92482201933613342193919 := by
  unfold tailWord_2431464
  simp only [CollatzResearch.WordTrace]
  refine ⟨44341388831614331917846723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59121851775485775890462297 44341388831614331917846723)
  ·
    refine ⟨66512083247421497876770085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44341388831614331917846723 66512083247421497876770085)
    ·
      refine ⟨12471015608891530851894391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66512083247421497876770085 12471015608891530851894391)
      ·
        refine ⟨18706523413337296277841587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12471015608891530851894391 18706523413337296277841587)
        ·
          refine ⟨28059785120005944416762381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18706523413337296277841587 28059785120005944416762381)
          ·
            refine ⟨10522419420002229156285893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28059785120005944416762381 10522419420002229156285893)
            ·
              refine ⟨1972953641250417966803605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10522419420002229156285893 1972953641250417966803605)
              ·
                refine ⟨92482201933613342193919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1972953641250417966803605 92482201933613342193919)
                ·
                  rfl

theorem cell22_2431464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 6].length) (baseStart_2431464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431464 prefixEnd_2431464 := by exact prefixLift 2431464
  have htrace : WordTrace (prefixWord ++ tailWord_2431464) baseStart_2431464 baseEnd_2431464 := by
    simpa [prefixWord, tailWord_2431464, baseEnd_2431464] using wordTrace_append hprefix tailTrace_2431464
  have hstable : (prefixWord ++ tailWord_2431464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431464).length < 2 ^ (prefixWord ++ tailWord_2431464).sum := by decide
  have hdescent : baseEnd_2431464 < baseStart_2431464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431507 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 1, 7]
def baseStart_2431507 : Nat := 118140960795 + 2431507 * 2 ^ 59
def prefixEnd_2431507 : Nat := 4983230072969 + 3 ^ 40 * 2431507 * 2
def baseEnd_2431507 : Nat := 832354537181282300920139

theorem tailTrace_2431507 : CollatzResearch.WordTrace tailWord_2431507 prefixEnd_2431507 832354537181282300920139 := by
  unfold tailWord_2431507
  simp only [CollatzResearch.WordTrace]
  refine ⟨88684346002072882179508775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59122897334715254786339183 88684346002072882179508775)
  ·
    refine ⟨133026519003109323269263163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88684346002072882179508775 133026519003109323269263163)
    ·
      refine ⟨199539778504663984903894745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133026519003109323269263163 199539778504663984903894745)
      ·
        refine ⟨149654833878497988677921059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199539778504663984903894745 149654833878497988677921059)
        ·
          refine ⟨224482250817746983016881589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149654833878497988677921059 224482250817746983016881589)
          ·
            refine ⟨21045211014163779657832649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 224482250817746983016881589 21045211014163779657832649)
            ·
              refine ⟨15783908260622834743374487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21045211014163779657832649 15783908260622834743374487)
              ·
                refine ⟨23675862390934252115061731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15783908260622834743374487 23675862390934252115061731)
                ·
                  refine ⟨35513793586401378172592597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23675862390934252115061731 35513793586401378172592597)
                  ·
                    refine ⟨832354537181282300920139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35513793586401378172592597 832354537181282300920139)
                    ·
                      rfl

theorem cell22_2431507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 7].length) (baseStart_2431507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431507 prefixEnd_2431507 := by exact prefixLift 2431507
  have htrace : WordTrace (prefixWord ++ tailWord_2431507) baseStart_2431507 baseEnd_2431507 := by
    simpa [prefixWord, tailWord_2431507, baseEnd_2431507] using wordTrace_append hprefix tailTrace_2431507
  have hstable : (prefixWord ++ tailWord_2431507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431507).length < 2 ^ (prefixWord ++ tailWord_2431507).sum := by decide
  have hdescent : baseEnd_2431507 < baseStart_2431507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431509 : List Nat := [1, 3, 2, 1, 3, 1, 3, 3, 5]
def baseStart_2431509 : Nat := 118140960795 + 2431509 * 2 ^ 59
def prefixEnd_2431509 : Nat := 4983230072969 + 3 ^ 40 * 2431509 * 2
def baseEnd_2431509 : Nat := 277451740607384987456711

theorem tailTrace_2431509 : CollatzResearch.WordTrace tailWord_2431509 prefixEnd_2431509 277451740607384987456711 := by
  unfold tailWord_2431509
  simp only [CollatzResearch.WordTrace]
  refine ⟨88684418948065636521081581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59122945965377091014054387 88684418948065636521081581)
  ·
    refine ⟨33256657105524613695405593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88684418948065636521081581 33256657105524613695405593)
    ·
      refine ⟨24942492829143460271554195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33256657105524613695405593 24942492829143460271554195)
      ·
        refine ⟨37413739243715190407331293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24942492829143460271554195 37413739243715190407331293)
        ·
          refine ⟨14030152216393196402749235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37413739243715190407331293 14030152216393196402749235)
          ·
            refine ⟨21045228324589794604123853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14030152216393196402749235 21045228324589794604123853)
            ·
              refine ⟨7891960621721172976546445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21045228324589794604123853 7891960621721172976546445)
              ·
                refine ⟨2959485233145439866204917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7891960621721172976546445 2959485233145439866204917)
                ·
                  refine ⟨277451740607384987456711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2959485233145439866204917 277451740607384987456711)
                  ·
                    rfl

theorem cell22_2431509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 5].length) (baseStart_2431509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431509 prefixEnd_2431509 := by exact prefixLift 2431509
  have htrace : WordTrace (prefixWord ++ tailWord_2431509) baseStart_2431509 baseEnd_2431509 := by
    simpa [prefixWord, tailWord_2431509, baseEnd_2431509] using wordTrace_append hprefix tailTrace_2431509
  have hstable : (prefixWord ++ tailWord_2431509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431509).length < 2 ^ (prefixWord ++ tailWord_2431509).sum := by decide
  have hdescent : baseEnd_2431509 < baseStart_2431509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431558 : List Nat := [6, 1, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_2431558 : Nat := 118140960795 + 2431558 * 2 ^ 59
def prefixEnd_2431558 : Nat := 4983230072969 + 3 ^ 40 * 2431558 * 2
def baseEnd_2431558 : Nat := 832371995523535167894983

theorem tailTrace_2431558 : CollatzResearch.WordTrace tailWord_2431558 prefixEnd_2431558 832371995523535167894983 := by
  unfold tailWord_2431558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2771443941402753684050479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59124137416592078593076885 2771443941402753684050479)
  ·
    refine ⟨4157165912104130526075719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2771443941402753684050479 4157165912104130526075719)
    ·
      refine ⟨6235748868156195789113579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4157165912104130526075719 6235748868156195789113579)
      ·
        refine ⟨9353623302234293683670369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6235748868156195789113579 9353623302234293683670369)
        ·
          refine ⟨7015217476675720262752777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9353623302234293683670369 7015217476675720262752777)
          ·
            refine ⟨5261413107506790197064583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7015217476675720262752777 5261413107506790197064583)
            ·
              refine ⟨7892119661260185295596875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5261413107506790197064583 7892119661260185295596875)
              ·
                refine ⟨11838179491890277943395313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7892119661260185295596875 11838179491890277943395313)
                ·
                  refine ⟨8878634618917708457546485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11838179491890277943395313 8878634618917708457546485)
                  ·
                    refine ⟨832371995523535167894983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8878634618917708457546485 832371995523535167894983)
                    ·
                      rfl

theorem cell22_2431558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_2431558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431558 prefixEnd_2431558 := by exact prefixLift 2431558
  have htrace : WordTrace (prefixWord ++ tailWord_2431558) baseStart_2431558 baseEnd_2431558 := by
    simpa [prefixWord, tailWord_2431558, baseEnd_2431558] using wordTrace_append hprefix tailTrace_2431558
  have hstable : (prefixWord ++ tailWord_2431558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431558).length < 2 ^ (prefixWord ++ tailWord_2431558).sum := by decide
  have hdescent : baseEnd_2431558 < baseStart_2431558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431569 : List Nat := [1, 2, 2, 1, 3, 3, 1, 3, 1, 5]
def baseStart_2431569 : Nat := 118140960795 + 2431569 * 2 ^ 59
def prefixEnd_2431569 : Nat := 4983230072969 + 3 ^ 40 * 2431569 * 2
def baseEnd_2431569 : Nat := 832375761048334805869949

theorem tailTrace_2431569 : CollatzResearch.WordTrace tailWord_2431569 prefixEnd_2431569 832375761048334805869949 := by
  unfold tailWord_2431569
  simp only [CollatzResearch.WordTrace]
  refine ⟨88686607327848266768265761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59124404885232177845510507 88686607327848266768265761)
  ·
    refine ⟨66514955495886200076199321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88686607327848266768265761 66514955495886200076199321)
    ·
      refine ⟨49886216621914650057149491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66514955495886200076199321 49886216621914650057149491)
      ·
        refine ⟨74829324932871975085724237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49886216621914650057149491 74829324932871975085724237)
        ·
          refine ⟨28060996849826990657146589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74829324932871975085724237 28060996849826990657146589)
          ·
            refine ⟨10522873818685121496429971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28060996849826990657146589 10522873818685121496429971)
            ·
              refine ⟨15784310728027682244644957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10522873818685121496429971 15784310728027682244644957)
              ·
                refine ⟨5919116523010380841741859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15784310728027682244644957 5919116523010380841741859)
                ·
                  refine ⟨8878674784515571262612789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5919116523010380841741859 8878674784515571262612789)
                  ·
                    refine ⟨832375761048334805869949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8878674784515571262612789 832375761048334805869949)
                    ·
                      rfl

theorem cell22_2431569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_2431569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431569 prefixEnd_2431569 := by exact prefixLift 2431569
  have htrace : WordTrace (prefixWord ++ tailWord_2431569) baseStart_2431569 baseEnd_2431569 := by
    simpa [prefixWord, tailWord_2431569, baseEnd_2431569] using wordTrace_append hprefix tailTrace_2431569
  have hstable : (prefixWord ++ tailWord_2431569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431569).length < 2 ^ (prefixWord ++ tailWord_2431569).sum := by decide
  have hdescent : baseEnd_2431569 < baseStart_2431569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431620 : List Nat := [2, 3, 2, 1, 3, 2, 3, 1, 2, 3]
def baseStart_2431620 : Nat := 118140960795 + 2431620 * 2 ^ 59
def prefixEnd_2431620 : Nat := 4983230072969 + 3 ^ 40 * 2431620 * 2
def baseEnd_2431620 : Nat := 832393219390587672844793

theorem tailTrace_2431620 : CollatzResearch.WordTrace tailWord_2431620 prefixEnd_2431620 832393219390587672844793 := by
  unfold tailWord_2431620
  simp only [CollatzResearch.WordTrace]
  refine ⟨44344233725331751239186157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59125644967109001652248209 44344233725331751239186157)
  ·
    refine ⟨16629087646999406714694809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44344233725331751239186157 16629087646999406714694809)
    ·
      refine ⟨12471815735249555036021107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16629087646999406714694809 12471815735249555036021107)
      ·
        refine ⟨18707723602874332554031661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12471815735249555036021107 18707723602874332554031661)
        ·
          refine ⟨7015396351077874707761873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18707723602874332554031661 7015396351077874707761873)
          ·
            refine ⟨5261547263308406030821405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7015396351077874707761873 5261547263308406030821405)
            ·
              refine ⟨1973080223740652261558027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5261547263308406030821405 1973080223740652261558027)
              ·
                refine ⟨2959620335610978392337041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1973080223740652261558027 2959620335610978392337041)
                ·
                  refine ⟨2219715251708233794252781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2959620335610978392337041 2219715251708233794252781)
                  ·
                    refine ⟨832393219390587672844793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2219715251708233794252781 832393219390587672844793)
                    ·
                      rfl

theorem cell22_2431620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_2431620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431620 prefixEnd_2431620 := by exact prefixLift 2431620
  have htrace : WordTrace (prefixWord ++ tailWord_2431620) baseStart_2431620 baseEnd_2431620 := by
    simpa [prefixWord, tailWord_2431620, baseEnd_2431620] using wordTrace_append hprefix tailTrace_2431620
  have hstable : (prefixWord ++ tailWord_2431620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431620).length < 2 ^ (prefixWord ++ tailWord_2431620).sum := by decide
  have hdescent : baseEnd_2431620 < baseStart_2431620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431661 : List Nat := [1, 5, 2, 1, 1, 2, 2, 1, 7]
def baseStart_2431661 : Nat := 118140960795 + 2431661 * 2 ^ 59
def prefixEnd_2431661 : Nat := 4983230072969 + 3 ^ 40 * 2431661 * 2
def baseEnd_2431661 : Nat := 277469084842825744189889

theorem tailTrace_2431661 : CollatzResearch.WordTrace tailWord_2431661 prefixEnd_2431661 277469084842825744189889 := by
  unfold tailWord_2431661
  simp only [CollatzResearch.WordTrace]
  refine ⟨88689962843514966480614837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59126641895676644320409891 88689962843514966480614837)
  ·
    refine ⟨8314684016579528107557641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88689962843514966480614837 8314684016579528107557641)
    ·
      refine ⟨6236013012434646080668231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8314684016579528107557641 6236013012434646080668231)
      ·
        refine ⟨9354019518651969121002347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6236013012434646080668231 9354019518651969121002347)
        ·
          refine ⟨14031029277977953681503521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9354019518651969121002347 14031029277977953681503521)
          ·
            refine ⟨10523271958483465261127641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14031029277977953681503521 10523271958483465261127641)
            ·
              refine ⟨7892453968862598945845731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10523271958483465261127641 7892453968862598945845731)
              ·
                refine ⟨11838680953293898418768597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7892453968862598945845731 11838680953293898418768597)
                ·
                  refine ⟨277469084842825744189889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11838680953293898418768597 277469084842825744189889)
                  ·
                    rfl

theorem cell22_2431661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_2431661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431661 prefixEnd_2431661 := by exact prefixLift 2431661
  have htrace : WordTrace (prefixWord ++ tailWord_2431661) baseStart_2431661 baseEnd_2431661 := by
    simpa [prefixWord, tailWord_2431661, baseEnd_2431661] using wordTrace_append hprefix tailTrace_2431661
  have hstable : (prefixWord ++ tailWord_2431661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431661).length < 2 ^ (prefixWord ++ tailWord_2431661).sum := by decide
  have hdescent : baseEnd_2431661 < baseStart_2431661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431721 : List Nat := [1, 2, 1, 1, 1, 2, 4, 3, 4, 3]
def baseStart_2431721 : Nat := 118140960795 + 2431721 * 2 ^ 59
def prefixEnd_2431721 : Nat := 4983230072969 + 3 ^ 40 * 2431721 * 2
def baseEnd_2431721 : Nat := 832427793754657076069483

theorem tailTrace_2431721 : CollatzResearch.WordTrace tailWord_2431721 prefixEnd_2431721 832427793754657076069483 := by
  unfold tailWord_2431721
  simp only [CollatzResearch.WordTrace]
  refine ⟨88692151223297596727799017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59128100815531731151866011 88692151223297596727799017)
  ·
    refine ⟨66519113417473197545849263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88692151223297596727799017 66519113417473197545849263)
    ·
      refine ⟨99778670126209796318773895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66519113417473197545849263 99778670126209796318773895)
      ·
        refine ⟨149668005189314694478160843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99778670126209796318773895 149668005189314694478160843)
        ·
          refine ⟨224502007783972041717241265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149668005189314694478160843 224502007783972041717241265)
          ·
            refine ⟨168376505837979031287930949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224502007783972041717241265 168376505837979031287930949)
            ·
              refine ⟨31570594844621068366487053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 168376505837979031287930949 31570594844621068366487053)
              ·
                refine ⟨11838973066732900637432645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31570594844621068366487053 11838973066732900637432645)
                ·
                  refine ⟨2219807450012418869518621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11838973066732900637432645 2219807450012418869518621)
                  ·
                    refine ⟨832427793754657076069483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2219807450012418869518621 832427793754657076069483)
                    ·
                      rfl

theorem cell22_2431721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 4, 3].length) (baseStart_2431721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431721 prefixEnd_2431721 := by exact prefixLift 2431721
  have htrace : WordTrace (prefixWord ++ tailWord_2431721) baseStart_2431721 baseEnd_2431721 := by
    simpa [prefixWord, tailWord_2431721, baseEnd_2431721] using wordTrace_append hprefix tailTrace_2431721
  have hstable : (prefixWord ++ tailWord_2431721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431721).length < 2 ^ (prefixWord ++ tailWord_2431721).sum := by decide
  have hdescent : baseEnd_2431721 < baseStart_2431721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431738 : List Nat := [3, 1, 1, 1, 1, 3, 4, 3, 2, 3]
def baseStart_2431738 : Nat := 118140960795 + 2431738 * 2 ^ 59
def prefixEnd_2431738 : Nat := 4983230072969 + 3 ^ 40 * 2431738 * 2
def baseEnd_2431738 : Nat := 832433613202074698394431

theorem tailTrace_2431738 : CollatzResearch.WordTrace tailWord_2431738 prefixEnd_2431738 832433613202074698394431 := by
  unfold tailWord_2431738
  simp only [CollatzResearch.WordTrace]
  refine ⟨22173192816059002157791967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59128514176157339087445245 22173192816059002157791967)
  ·
    refine ⟨33259789224088503236687951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22173192816059002157791967 33259789224088503236687951)
    ·
      refine ⟨49889683836132754855031927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33259789224088503236687951 49889683836132754855031927)
      ·
        refine ⟨74834525754199132282547891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49889683836132754855031927 74834525754199132282547891)
        ·
          refine ⟨112251788631298698423821837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74834525754199132282547891 112251788631298698423821837)
          ·
            refine ⟨42094420736737011908933189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112251788631298698423821837 42094420736737011908933189)
            ·
              refine ⟨7892703888138189732924973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42094420736737011908933189 7892703888138189732924973)
              ·
                refine ⟨2959763958051821149846865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7892703888138189732924973 2959763958051821149846865)
                ·
                  refine ⟨2219822968538865862385149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2959763958051821149846865 2219822968538865862385149)
                  ·
                    refine ⟨832433613202074698394431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2219822968538865862385149 832433613202074698394431)
                    ·
                      rfl

theorem cell22_2431738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 2, 3].length) (baseStart_2431738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431738 prefixEnd_2431738 := by exact prefixLift 2431738
  have htrace : WordTrace (prefixWord ++ tailWord_2431738) baseStart_2431738 baseEnd_2431738 := by
    simpa [prefixWord, tailWord_2431738, baseEnd_2431738] using wordTrace_append hprefix tailTrace_2431738
  have hstable : (prefixWord ++ tailWord_2431738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431738).length < 2 ^ (prefixWord ++ tailWord_2431738).sum := by decide
  have hdescent : baseEnd_2431738 < baseStart_2431738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431789 : List Nat := [1, 5, 3, 2, 2, 1, 1, 1, 1, 5]
def baseStart_2431789 : Nat := 118140960795 + 2431789 * 2 ^ 59
def prefixEnd_2431789 : Nat := 4983230072969 + 3 ^ 40 * 2431789 * 2
def baseEnd_2431789 : Nat := 832451071544327565369275

theorem tailTrace_2431789 : CollatzResearch.WordTrace tailWord_2431789 prefixEnd_2431789 832451071544327565369275 := by
  unfold tailWord_2431789
  simp only [CollatzResearch.WordTrace]
  refine ⟨88694631387051244341274421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59129754258034162894182947 88694631387051244341274421)
  ·
    refine ⟨8315121692536054156994477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88694631387051244341274421 8315121692536054156994477)
    ·
      refine ⟨3118170634701020308872929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8315121692536054156994477 3118170634701020308872929)
      ·
        refine ⟨2338627976025765231654697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3118170634701020308872929 2338627976025765231654697)
        ·
          refine ⟨1753970982019323923741023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2338627976025765231654697 1753970982019323923741023)
          ·
            refine ⟨2630956473028985885611535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1753970982019323923741023 2630956473028985885611535)
            ·
              refine ⟨3946434709543478828417303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2630956473028985885611535 3946434709543478828417303)
              ·
                refine ⟨5919652064315218242625955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3946434709543478828417303 5919652064315218242625955)
                ·
                  refine ⟨8879478096472827363938933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5919652064315218242625955 8879478096472827363938933)
                  ·
                    refine ⟨832451071544327565369275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8879478096472827363938933 832451071544327565369275)
                    ·
                      rfl

theorem cell22_2431789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_2431789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431789 prefixEnd_2431789 := by exact prefixLift 2431789
  have htrace : WordTrace (prefixWord ++ tailWord_2431789) baseStart_2431789 baseEnd_2431789 := by
    simpa [prefixWord, tailWord_2431789, baseEnd_2431789] using wordTrace_append hprefix tailTrace_2431789
  have hstable : (prefixWord ++ tailWord_2431789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431789).length < 2 ^ (prefixWord ++ tailWord_2431789).sum := by decide
  have hdescent : baseEnd_2431789 < baseStart_2431789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431817 : List Nat := [1, 2, 1, 1, 2, 7, 1, 3, 1, 3]
def baseStart_2431817 : Nat := 118140960795 + 2431817 * 2 ^ 59
def prefixEnd_2431817 : Nat := 4983230072969 + 3 ^ 40 * 2431817 * 2
def baseEnd_2431817 : Nat := 832460656516544825669189

theorem tailTrace_2431817 : CollatzResearch.WordTrace tailWord_2431817 prefixEnd_2431817 832460656516544825669189 := by
  unfold tailWord_2431817
  simp only [CollatzResearch.WordTrace]
  refine ⟨88695652630949805123293705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59130435087299870082195803 88695652630949805123293705)
  ·
    refine ⟨66521739473212353842470279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88695652630949805123293705 66521739473212353842470279)
    ·
      refine ⟨99782609209818530763705419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66521739473212353842470279 99782609209818530763705419)
      ·
        refine ⟨149673913814727796145558129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99782609209818530763705419 149673913814727796145558129)
        ·
          refine ⟨112255435361045847109168597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149673913814727796145558129 112255435361045847109168597)
          ·
            refine ⟨2630986766274512041621139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 112255435361045847109168597 2630986766274512041621139)
            ·
              refine ⟨3946480149411768062431709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2630986766274512041621139 3946480149411768062431709)
              ·
                refine ⟨1479930056029413023411891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3946480149411768062431709 1479930056029413023411891)
                ·
                  refine ⟨2219895084044119535117837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1479930056029413023411891 2219895084044119535117837)
                  ·
                    refine ⟨832460656516544825669189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2219895084044119535117837 832460656516544825669189)
                    ·
                      rfl

theorem cell22_2431817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 3, 1, 3].length) (baseStart_2431817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431817 prefixEnd_2431817 := by exact prefixLift 2431817
  have htrace : WordTrace (prefixWord ++ tailWord_2431817) baseStart_2431817 baseEnd_2431817 := by
    simpa [prefixWord, tailWord_2431817, baseEnd_2431817] using wordTrace_append hprefix tailTrace_2431817
  have hstable : (prefixWord ++ tailWord_2431817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431817).length < 2 ^ (prefixWord ++ tailWord_2431817).sum := by decide
  have hdescent : baseEnd_2431817 < baseStart_2431817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431841 : List Nat := [1, 2, 3, 1, 1, 1, 2, 5, 6]
def baseStart_2431841 : Nat := 118140960795 + 2431841 * 2 ^ 59
def prefixEnd_2431841 : Nat := 4983230072969 + 3 ^ 40 * 2431841 * 2
def baseEnd_2431841 : Nat := 277489624069005587689705

theorem tailTrace_2431841 : CollatzResearch.WordTrace tailWord_2431841 prefixEnd_2431841 277489624069005587689705 := by
  unfold tailWord_2431841
  simp only [CollatzResearch.WordTrace]
  refine ⟨88696527982862857222167377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59131018655241904814778251 88696527982862857222167377)
  ·
    refine ⟨66522395987147142916625533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88696527982862857222167377 66522395987147142916625533)
    ·
      refine ⟨24945898495180178593734575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66522395987147142916625533 24945898495180178593734575)
      ·
        refine ⟨37418847742770267890601863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24945898495180178593734575 37418847742770267890601863)
        ·
          refine ⟨56128271614155401835902795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37418847742770267890601863 56128271614155401835902795)
          ·
            refine ⟨84192407421233102753854193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56128271614155401835902795 84192407421233102753854193)
            ·
              refine ⟨63144305565924827065390645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84192407421233102753854193 63144305565924827065390645)
              ·
                refine ⟨5919778646805452537380373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63144305565924827065390645 5919778646805452537380373)
                ·
                  refine ⟨277489624069005587689705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5919778646805452537380373 277489624069005587689705)
                  ·
                    rfl

theorem cell22_2431841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 6].length) (baseStart_2431841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431841 prefixEnd_2431841 := by exact prefixLift 2431841
  have htrace : WordTrace (prefixWord ++ tailWord_2431841) baseStart_2431841 baseEnd_2431841 := by
    simpa [prefixWord, tailWord_2431841, baseEnd_2431841] using wordTrace_append hprefix tailTrace_2431841
  have hstable : (prefixWord ++ tailWord_2431841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431841).length < 2 ^ (prefixWord ++ tailWord_2431841).sum := by decide
  have hdescent : baseEnd_2431841 < baseStart_2431841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431871 : List Nat := [1, 1, 2, 2, 1, 1, 4, 3, 1, 6]
def baseStart_2431871 : Nat := 118140960795 + 2431871 * 2 ^ 59
def prefixEnd_2431871 : Nat := 4983230072969 + 3 ^ 40 * 2431871 * 2
def baseEnd_2431871 : Nat := 832479141820106684819023

theorem tailTrace_2431871 : CollatzResearch.WordTrace tailWord_2431871 prefixEnd_2431871 832479141820106684819023 := by
  unfold tailWord_2431871
  simp only [CollatzResearch.WordTrace]
  refine ⟨88697622172754172345759467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59131748115169448230506311 88697622172754172345759467)
  ·
    refine ⟨133046433259131258518639201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88697622172754172345759467 133046433259131258518639201)
    ·
      refine ⟨99784824944348443888979401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133046433259131258518639201 99784824944348443888979401)
      ·
        refine ⟨74838618708261332916734551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99784824944348443888979401 74838618708261332916734551)
        ·
          refine ⟨112257928062391999375101827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74838618708261332916734551 112257928062391999375101827)
          ·
            refine ⟨168386892093587999062652741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112257928062391999375101827 168386892093587999062652741)
            ·
              refine ⟨31572542267547749824247389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 168386892093587999062652741 31572542267547749824247389)
              ·
                refine ⟨11839703350330406184092771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31572542267547749824247389 11839703350330406184092771)
                ·
                  refine ⟨17759555025495609276139157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11839703350330406184092771 17759555025495609276139157)
                  ·
                    refine ⟨832479141820106684819023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17759555025495609276139157 832479141820106684819023)
                    ·
                      rfl

theorem cell22_2431871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 6].length) (baseStart_2431871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431871 prefixEnd_2431871 := by exact prefixLift 2431871
  have htrace : WordTrace (prefixWord ++ tailWord_2431871) baseStart_2431871 baseEnd_2431871 := by
    simpa [prefixWord, tailWord_2431871, baseEnd_2431871] using wordTrace_append hprefix tailTrace_2431871
  have hstable : (prefixWord ++ tailWord_2431871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431871).length < 2 ^ (prefixWord ++ tailWord_2431871).sum := by decide
  have hdescent : baseEnd_2431871 < baseStart_2431871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431886 : List Nat := [4, 1, 1, 16]
def baseStart_2431886 : Nat := 118140960795 + 2431886 * 2 ^ 59
def prefixEnd_2431886 : Nat := 4983230072969 + 3 ^ 40 * 2431886 * 2
def baseEnd_2431886 : Nat := 1141953740228603080513

theorem tailTrace_2431886 : CollatzResearch.WordTrace tailWord_2431886 prefixEnd_2431886 1141953740228603080513 := by
  unfold tailWord_2431886
  simp only [CollatzResearch.WordTrace]
  refine ⟨11087271158462478738444439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59132112845133219938370341 11087271158462478738444439)
  ·
    refine ⟨16630906737693718107666659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11087271158462478738444439 16630906737693718107666659)
    ·
      refine ⟨24946360106540577161499989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16630906737693718107666659 24946360106540577161499989)
      ·
        refine ⟨1141953740228603080513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 24946360106540577161499989 1141953740228603080513)
        ·
          rfl

theorem cell22_2431886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 16].length) (baseStart_2431886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431886 prefixEnd_2431886 := by exact prefixLift 2431886
  have htrace : WordTrace (prefixWord ++ tailWord_2431886) baseStart_2431886 baseEnd_2431886 := by
    simpa [prefixWord, tailWord_2431886, baseEnd_2431886] using wordTrace_append hprefix tailTrace_2431886
  have hstable : (prefixWord ++ tailWord_2431886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431886).length < 2 ^ (prefixWord ++ tailWord_2431886).sum := by decide
  have hdescent : baseEnd_2431886 < baseStart_2431886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431903 : List Nat := [1, 1, 2, 5, 2, 1, 3, 7]
def baseStart_2431903 : Nat := 118140960795 + 2431903 * 2 ^ 59
def prefixEnd_2431903 : Nat := 4983230072969 + 3 ^ 40 * 2431903 * 2
def baseEnd_2431903 : Nat := 92498899563785474224325

theorem tailTrace_2431903 : CollatzResearch.WordTrace tailWord_2431903 prefixEnd_2431903 92498899563785474224325 := by
  unfold tailWord_2431903
  simp only [CollatzResearch.WordTrace]
  refine ⟨88698789308638241810924363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59132526205758827873949575 88698789308638241810924363)
  ·
    refine ⟨133048183962957362716386545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88698789308638241810924363 133048183962957362716386545)
    ·
      refine ⟨99786137972218022037289909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133048183962957362716386545 99786137972218022037289909)
      ·
        refine ⟨9354950434895439565995929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99786137972218022037289909 9354950434895439565995929)
        ·
          refine ⟨7016212826171579674496947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9354950434895439565995929 7016212826171579674496947)
          ·
            refine ⟨10524319239257369511745421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7016212826171579674496947 10524319239257369511745421)
            ·
              refine ⟨3946619714721513566904533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10524319239257369511745421 3946619714721513566904533)
              ·
                refine ⟨92498899563785474224325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3946619714721513566904533 92498899563785474224325)
                ·
                  rfl

theorem cell22_2431903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 7].length) (baseStart_2431903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431903 prefixEnd_2431903 := by exact prefixLift 2431903
  have htrace : WordTrace (prefixWord ++ tailWord_2431903) baseStart_2431903 baseEnd_2431903 := by
    simpa [prefixWord, tailWord_2431903, baseEnd_2431903] using wordTrace_append hprefix tailTrace_2431903
  have hstable : (prefixWord ++ tailWord_2431903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431903).length < 2 ^ (prefixWord ++ tailWord_2431903).sum := by decide
  have hdescent : baseEnd_2431903 < baseStart_2431903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431948 : List Nat := [2, 2, 1, 4, 1, 1, 3, 1, 7]
def baseStart_2431948 : Nat := 118140960795 + 2431948 * 2 ^ 59
def prefixEnd_2431948 : Nat := 4983230072969 + 3 ^ 40 * 2431948 * 2
def baseEnd_2431948 : Nat := 277501833497901383547929

theorem tailTrace_2431948 : CollatzResearch.WordTrace tailWord_2431948 prefixEnd_2431948 277501833497901383547929 := by
  unfold tailWord_2431948
  simp only [CollatzResearch.WordTrace]
  refine ⟨44350215296737607248156249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59133620395650142997541665 44350215296737607248156249)
  ·
    refine ⟨33262661472553205436117187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44350215296737607248156249 33262661472553205436117187)
    ·
      refine ⟨49893992208829808154175781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33262661472553205436117187 49893992208829808154175781)
      ·
        refine ⟨9355123539155589028907959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49893992208829808154175781 9355123539155589028907959)
        ·
          refine ⟨14032685308733383543361939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9355123539155589028907959 14032685308733383543361939)
          ·
            refine ⟨21049027963100075315042909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14032685308733383543361939 21049027963100075315042909)
            ·
              refine ⟨7893385486162528243141091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21049027963100075315042909 7893385486162528243141091)
              ·
                refine ⟨11840078229243792364711637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7893385486162528243141091 11840078229243792364711637)
                ·
                  refine ⟨277501833497901383547929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11840078229243792364711637 277501833497901383547929)
                  ·
                    rfl

theorem cell22_2431948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 7].length) (baseStart_2431948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2431948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2431948 prefixEnd_2431948 := by exact prefixLift 2431948
  have htrace : WordTrace (prefixWord ++ tailWord_2431948) baseStart_2431948 baseEnd_2431948 := by
    simpa [prefixWord, tailWord_2431948, baseEnd_2431948] using wordTrace_append hprefix tailTrace_2431948
  have hstable : (prefixWord ++ tailWord_2431948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431948).length < 2 ^ (prefixWord ++ tailWord_2431948).sum := by decide
  have hdescent : baseEnd_2431948 < baseStart_2431948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432010 : List Nat := [3, 1, 2, 2, 3, 1, 3, 1, 6]
def baseStart_2432010 : Nat := 118140960795 + 2432010 * 2 ^ 59
def prefixEnd_2432010 : Nat := 4983230072969 + 3 ^ 40 * 2432010 * 2
def baseEnd_2432010 : Nat := 277508908120252218531199

theorem tailTrace_2432010 : CollatzResearch.WordTrace tailWord_2432010 prefixEnd_2432010 277508908120252218531199 := by
  unfold tailWord_2432010
  simp only [CollatzResearch.WordTrace]
  refine ⟨22175672979812649771267371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59135127946167066056712989 22175672979812649771267371)
  ·
    refine ⟨33263509469718974656901057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22175672979812649771267371 33263509469718974656901057)
    ·
      refine ⟨24947632102289230992675793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33263509469718974656901057 24947632102289230992675793)
      ·
        refine ⟨18710724076716923244506845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24947632102289230992675793 18710724076716923244506845)
        ·
          refine ⟨7016521528768846216690067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18710724076716923244506845 7016521528768846216690067)
          ·
            refine ⟨10524782293153269325035101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7016521528768846216690067 10524782293153269325035101)
            ·
              refine ⟨3946793359932475996888163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10524782293153269325035101 3946793359932475996888163)
              ·
                refine ⟨5920190039898713995332245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3946793359932475996888163 5920190039898713995332245)
                ·
                  refine ⟨277508908120252218531199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5920190039898713995332245 277508908120252218531199)
                  ·
                    rfl

theorem cell22_2432010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 6].length) (baseStart_2432010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2432010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2432010 prefixEnd_2432010 := by exact prefixLift 2432010
  have htrace : WordTrace (prefixWord ++ tailWord_2432010) baseStart_2432010 baseEnd_2432010 := by
    simpa [prefixWord, tailWord_2432010, baseEnd_2432010] using wordTrace_append hprefix tailTrace_2432010
  have hstable : (prefixWord ++ tailWord_2432010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432010).length < 2 ^ (prefixWord ++ tailWord_2432010).sum := by decide
  have hdescent : baseEnd_2432010 < baseStart_2432010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432029 : List Nat := [1, 4, 2, 2, 3, 2, 1, 2, 1, 4]
def baseStart_2432029 : Nat := 118140960795 + 2432029 * 2 ^ 59
def prefixEnd_2432029 : Nat := 4983230072969 + 3 ^ 40 * 2432029 * 2
def baseEnd_2432029 : Nat := 832533228449046939368539

theorem tailTrace_2432029 : CollatzResearch.WordTrace tailWord_2432029 prefixEnd_2432029 832533228449046939368539 := by
  unfold tailWord_2432029
  simp only [CollatzResearch.WordTrace]
  refine ⟨88703384906181765330011141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59135589937454510220007427 88703384906181765330011141)
  ·
    refine ⟨16631884669909080999377089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88703384906181765330011141 16631884669909080999377089)
    ·
      refine ⟨12473913502431810749532817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16631884669909080999377089 12473913502431810749532817)
      ·
        refine ⟨9355435126823858062149613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12473913502431810749532817 9355435126823858062149613)
        ·
          refine ⟨3508288172558946773306105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9355435126823858062149613 3508288172558946773306105)
          ·
            refine ⟨2631216129419210079979579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3508288172558946773306105 2631216129419210079979579)
            ·
              refine ⟨3946824194128815119969369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2631216129419210079979579 3946824194128815119969369)
              ·
                refine ⟨2960118145596611339977027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3946824194128815119969369 2960118145596611339977027)
                ·
                  refine ⟨4440177218394917009965541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2960118145596611339977027 4440177218394917009965541)
                  ·
                    refine ⟨832533228449046939368539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4440177218394917009965541 832533228449046939368539)
                    ·
                      rfl

theorem cell22_2432029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_2432029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2432029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2432029 prefixEnd_2432029 := by exact prefixLift 2432029
  have htrace : WordTrace (prefixWord ++ tailWord_2432029) baseStart_2432029 baseEnd_2432029 := by
    simpa [prefixWord, tailWord_2432029, baseEnd_2432029] using wordTrace_append hprefix tailTrace_2432029
  have hstable : (prefixWord ++ tailWord_2432029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432029).length < 2 ^ (prefixWord ++ tailWord_2432029).sum := by decide
  have hdescent : baseEnd_2432029 < baseStart_2432029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432042 : List Nat := [3, 1, 4, 1, 3, 1, 1, 2, 1, 5]
def baseStart_2432042 : Nat := 118140960795 + 2432042 * 2 ^ 59
def prefixEnd_2432042 : Nat := 4983230072969 + 3 ^ 40 * 2432042 * 2
def baseEnd_2432042 : Nat := 832537678614719238793499

theorem tailTrace_2432042 : CollatzResearch.WordTrace tailWord_2432042 prefixEnd_2432042 832537678614719238793499 := by
  unfold tailWord_2432042
  simp only [CollatzResearch.WordTrace]
  refine ⟨22175964763783667137558595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59135906036756445700156253 22175964763783667137558595)
  ·
    refine ⟨33263947145675500706337893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22175964763783667137558595 33263947145675500706337893)
    ·
      refine ⟨6236990089814156382438355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33263947145675500706337893 6236990089814156382438355)
      ·
        refine ⟨9355485134721234573657533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6236990089814156382438355 9355485134721234573657533)
        ·
          refine ⟨3508306925520462965121575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9355485134721234573657533 3508306925520462965121575)
          ·
            refine ⟨5262460388280694447682363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3508306925520462965121575 5262460388280694447682363)
            ·
              refine ⟨7893690582421041671523545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5262460388280694447682363 7893690582421041671523545)
              ·
                refine ⟨5920267936815781253642659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7893690582421041671523545 5920267936815781253642659)
                ·
                  refine ⟨8880401905223671880463989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5920267936815781253642659 8880401905223671880463989)
                  ·
                    refine ⟨832537678614719238793499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8880401905223671880463989 832537678614719238793499)
                    ·
                      rfl

theorem cell22_2432042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_2432042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2432042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2432042 prefixEnd_2432042 := by exact prefixLift 2432042
  have htrace : WordTrace (prefixWord ++ tailWord_2432042) baseStart_2432042 baseEnd_2432042 := by
    simpa [prefixWord, tailWord_2432042, baseEnd_2432042] using wordTrace_append hprefix tailTrace_2432042
  have hstable : (prefixWord ++ tailWord_2432042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432042).length < 2 ^ (prefixWord ++ tailWord_2432042).sum := by decide
  have hdescent : baseEnd_2432042 < baseStart_2432042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432160 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 3, 5]
def baseStart_2432160 : Nat := 118140960795 + 2432160 * 2 ^ 59
def prefixEnd_2432160 : Nat := 4983230072969 + 3 ^ 40 * 2432160 * 2
def baseEnd_2432160 : Nat := 832578072426206264343137

theorem tailTrace_2432160 : CollatzResearch.WordTrace tailWord_2432160 prefixEnd_2432160 832578072426206264343137 := by
  unfold tailWord_2432160
  simp only [CollatzResearch.WordTrace]
  refine ⟨44354081434353587351514967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59138775245804783135353289 44354081434353587351514967)
  ·
    refine ⟨66531122151530381027272451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44354081434353587351514967 66531122151530381027272451)
    ·
      refine ⟨99796683227295571540908677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66531122151530381027272451 99796683227295571540908677)
      ·
        refine ⟨18711878105117919663920377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99796683227295571540908677 18711878105117919663920377)
        ·
          refine ⟨14033908578838439747940283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18711878105117919663920377 14033908578838439747940283)
          ·
            refine ⟨21050862868257659621910425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14033908578838439747940283 21050862868257659621910425)
            ·
              refine ⟨15788147151193244716432819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21050862868257659621910425 15788147151193244716432819)
              ·
                refine ⟨23682220726789867074649229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15788147151193244716432819 23682220726789867074649229)
                ·
                  refine ⟨8880832772546200152993461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23682220726789867074649229 8880832772546200152993461)
                  ·
                    refine ⟨832578072426206264343137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8880832772546200152993461 832578072426206264343137)
                    ·
                      rfl

theorem cell22_2432160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 3, 5].length) (baseStart_2432160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2432160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2432160 prefixEnd_2432160 := by exact prefixLift 2432160
  have htrace : WordTrace (prefixWord ++ tailWord_2432160) baseStart_2432160 baseEnd_2432160 := by
    simpa [prefixWord, tailWord_2432160, baseEnd_2432160] using wordTrace_append hprefix tailTrace_2432160
  have hstable : (prefixWord ++ tailWord_2432160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432160).length < 2 ^ (prefixWord ++ tailWord_2432160).sum := by decide
  have hdescent : baseEnd_2432160 < baseStart_2432160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432175 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 4, 4]
def baseStart_2432175 : Nat := 118140960795 + 2432175 * 2 ^ 59
def prefixEnd_2432175 : Nat := 4983230072969 + 3 ^ 40 * 2432175 * 2
def baseEnd_2432175 : Nat := 832583207232751225218091

theorem tailTrace_2432175 : CollatzResearch.WordTrace tailWord_2432175 prefixEnd_2432175 832583207232751225218091 := by
  unfold tailWord_2432175
  simp only [CollatzResearch.WordTrace]
  refine ⟨88708709963652832264825979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59139139975768554843217319 88708709963652832264825979)
  ·
    refine ⟨133063064945479248397238969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88708709963652832264825979 133063064945479248397238969)
    ·
      refine ⟨99797298709109436297929227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133063064945479248397238969 99797298709109436297929227)
      ·
        refine ⟨149695948063664154446893841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99797298709109436297929227 149695948063664154446893841)
        ·
          refine ⟨112271961047748115835170381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149695948063664154446893841 112271961047748115835170381)
          ·
            refine ⟨42101985392905543438188893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112271961047748115835170381 42101985392905543438188893)
            ·
              refine ⟨15788244522339578789320835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42101985392905543438188893 15788244522339578789320835)
              ·
                refine ⟨23682366783509368183981253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15788244522339578789320835 23682366783509368183981253)
                ·
                  refine ⟨4440443771908006534496485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23682366783509368183981253 4440443771908006534496485)
                  ·
                    refine ⟨832583207232751225218091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4440443771908006534496485 832583207232751225218091)
                    ·
                      rfl

theorem cell22_2432175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 4].length) (baseStart_2432175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2432175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2432175 prefixEnd_2432175 := by exact prefixLift 2432175
  have htrace : WordTrace (prefixWord ++ tailWord_2432175) baseStart_2432175 baseEnd_2432175 := by
    simpa [prefixWord, tailWord_2432175, baseEnd_2432175] using wordTrace_append hprefix tailTrace_2432175
  have hstable : (prefixWord ++ tailWord_2432175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432175).length < 2 ^ (prefixWord ++ tailWord_2432175).sum := by decide
  have hdescent : baseEnd_2432175 < baseStart_2432175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432198 : List Nat := [6, 1, 2, 2, 1, 1, 1, 1, 3, 4]
def baseStart_2432198 : Nat := 118140960795 + 2432198 * 2 ^ 59
def prefixEnd_2432198 : Nat := 4983230072969 + 3 ^ 40 * 2432198 * 2
def baseEnd_2432198 : Nat := 832591080602786831893021

theorem tailTrace_2432198 : CollatzResearch.WordTrace tailWord_2432198 prefixEnd_2432198 832591080602786831893021 := by
  unfold tailWord_2432198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2772173401330297099778539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59139699228379671461942165 2772173401330297099778539)
  ·
    refine ⟨4158260101995445649667809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2772173401330297099778539 4158260101995445649667809)
    ·
      refine ⟨3118695076496584237250857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4158260101995445649667809 3118695076496584237250857)
      ·
        refine ⟨2339021307372438177938143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3118695076496584237250857 2339021307372438177938143)
        ·
          refine ⟨3508531961058657266907215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2339021307372438177938143 3508531961058657266907215)
          ·
            refine ⟨5262797941587985900360823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3508531961058657266907215 5262797941587985900360823)
            ·
              refine ⟨7894196912381978850541235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5262797941587985900360823 7894196912381978850541235)
              ·
                refine ⟨11841295368572968275811853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7894196912381978850541235 11841295368572968275811853)
                ·
                  refine ⟨4440485763214863103429445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11841295368572968275811853 4440485763214863103429445)
                  ·
                    refine ⟨832591080602786831893021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4440485763214863103429445 832591080602786831893021)
                    ·
                      rfl

theorem cell22_2432198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_2432198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2432198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2432198 prefixEnd_2432198 := by exact prefixLift 2432198
  have htrace : WordTrace (prefixWord ++ tailWord_2432198) baseStart_2432198 baseEnd_2432198 := by
    simpa [prefixWord, tailWord_2432198, baseEnd_2432198] using wordTrace_append hprefix tailTrace_2432198
  have hstable : (prefixWord ++ tailWord_2432198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432198).length < 2 ^ (prefixWord ++ tailWord_2432198).sum := by decide
  have hdescent : baseEnd_2432198 < baseStart_2432198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432237 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 2, 6]
def baseStart_2432237 : Nat := 118140960795 + 2432237 * 2 ^ 59
def prefixEnd_2432237 : Nat := 4983230072969 + 3 ^ 40 * 2432237 * 2
def baseEnd_2432237 : Nat := 832604431099803730167901

theorem tailTrace_2432237 : CollatzResearch.WordTrace tailWord_2432237 prefixEnd_2432237 832604431099803730167901 := by
  unfold tailWord_2432237
  simp only [CollatzResearch.WordTrace]
  refine ⟨88710971289428216853582965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59140647526285477902388643 88710971289428216853582965)
  ·
    refine ⟨8316653558383895330023403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88710971289428216853582965 8316653558383895330023403)
    ·
      refine ⟨12474980337575842995035105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8316653558383895330023403 12474980337575842995035105)
      ·
        refine ⟨9356235253181882246276329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12474980337575842995035105 9356235253181882246276329)
        ·
          refine ⟨7017176439886411684707247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9356235253181882246276329 7017176439886411684707247)
          ·
            refine ⟨10525764659829617527060871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7017176439886411684707247 10525764659829617527060871)
            ·
              refine ⟨15788646989744426290591307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10525764659829617527060871 15788646989744426290591307)
              ·
                refine ⟨23682970484616639435886961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15788646989744426290591307 23682970484616639435886961)
                ·
                  refine ⟨17762227863462479576915221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23682970484616639435886961 17762227863462479576915221)
                  ·
                    refine ⟨832604431099803730167901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17762227863462479576915221 832604431099803730167901)
                    ·
                      rfl

theorem cell22_2432237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_2432237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2432237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2432237 prefixEnd_2432237 := by exact prefixLift 2432237
  have htrace : WordTrace (prefixWord ++ tailWord_2432237) baseStart_2432237 baseEnd_2432237 := by
    simpa [prefixWord, tailWord_2432237, baseEnd_2432237] using wordTrace_append hprefix tailTrace_2432237
  have hstable : (prefixWord ++ tailWord_2432237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432237).length < 2 ^ (prefixWord ++ tailWord_2432237).sum := by decide
  have hdescent : baseEnd_2432237 < baseStart_2432237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432286 : List Nat := [4, 3, 2, 1, 2, 1, 1, 1, 7]
def baseStart_2432286 : Nat := 118140960795 + 2432286 * 2 ^ 59
def prefixEnd_2432286 : Nat := 4983230072969 + 3 ^ 40 * 2432286 * 2
def baseEnd_2432286 : Nat := 277540401600394645230917

theorem tailTrace_2432286 : CollatzResearch.WordTrace tailWord_2432286 prefixEnd_2432286 277540401600394645230917 := by
  unfold tailWord_2432286
  simp only [CollatzResearch.WordTrace]
  refine ⟨11089094808281337277764589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59141838977500465481411141 11089094808281337277764589)
  ·
    refine ⟨4158410553105501479161721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11089094808281337277764589 4158410553105501479161721)
    ·
      refine ⟨3118807914829126109371291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4158410553105501479161721 3118807914829126109371291)
      ·
        refine ⟨4678211872243689164056937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3118807914829126109371291 4678211872243689164056937)
        ·
          refine ⟨3508658904182766873042703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4678211872243689164056937 3508658904182766873042703)
          ·
            refine ⟨5262988356274150309564055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3508658904182766873042703 5262988356274150309564055)
            ·
              refine ⟨7894482534411225464346083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5262988356274150309564055 7894482534411225464346083)
              ·
                refine ⟨11841723801616838196519125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7894482534411225464346083 11841723801616838196519125)
                ·
                  refine ⟨277540401600394645230917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11841723801616838196519125 277540401600394645230917)
                  ·
                    rfl

theorem cell22_2432286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_2432286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2432286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2432286 prefixEnd_2432286 := by exact prefixLift 2432286
  have htrace : WordTrace (prefixWord ++ tailWord_2432286) baseStart_2432286 baseEnd_2432286 := by
    simpa [prefixWord, tailWord_2432286, baseEnd_2432286] using wordTrace_append hprefix tailTrace_2432286
  have hstable : (prefixWord ++ tailWord_2432286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432286).length < 2 ^ (prefixWord ++ tailWord_2432286).sum := by decide
  have hdescent : baseEnd_2432286 < baseStart_2432286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432327 : List Nat := [1, 1, 4, 1, 2, 3, 2, 1, 1, 6]
def baseStart_2432327 : Nat := 118140960795 + 2432327 * 2 ^ 59
def prefixEnd_2432327 : Nat := 4983230072969 + 3 ^ 40 * 2432327 * 2
def baseEnd_2432327 : Nat := 832635239939073495417625

theorem tailTrace_2432327 : CollatzResearch.WordTrace tailWord_2432327 prefixEnd_2432327 832635239939073495417625 := by
  unfold tailWord_2432327
  simp only [CollatzResearch.WordTrace]
  refine ⟨88714253859102162224359235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59142835906068108149572823 88714253859102162224359235)
  ·
    refine ⟨133071380788653243336538853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88714253859102162224359235 133071380788653243336538853)
    ·
      refine ⟨24950883897872483125601035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133071380788653243336538853 24950883897872483125601035)
      ·
        refine ⟨37426325846808724688401553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24950883897872483125601035 37426325846808724688401553)
        ·
          refine ⟨28069744385106543516301165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37426325846808724688401553 28069744385106543516301165)
          ·
            refine ⟨10526154144414953818612937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28069744385106543516301165 10526154144414953818612937)
            ·
              refine ⟨7894615608311215363959703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10526154144414953818612937 7894615608311215363959703)
              ·
                refine ⟨11841923412466823045939555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7894615608311215363959703 11841923412466823045939555)
                ·
                  refine ⟨17762885118700234568909333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11841923412466823045939555 17762885118700234568909333)
                  ·
                    refine ⟨832635239939073495417625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17762885118700234568909333 832635239939073495417625)
                    ·
                      rfl

theorem cell22_2432327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_2432327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2432327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2432327 prefixEnd_2432327 := by exact prefixLift 2432327
  have htrace : WordTrace (prefixWord ++ tailWord_2432327) baseStart_2432327 baseEnd_2432327 := by
    simpa [prefixWord, tailWord_2432327, baseEnd_2432327] using wordTrace_append hprefix tailTrace_2432327
  have hstable : (prefixWord ++ tailWord_2432327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432327).length < 2 ^ (prefixWord ++ tailWord_2432327).sum := by decide
  have hdescent : baseEnd_2432327 < baseStart_2432327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432359 : List Nat := [1, 1, 5, 1, 4, 1, 2, 7]
def baseStart_2432359 : Nat := 118140960795 + 2432359 * 2 ^ 59
def prefixEnd_2432359 : Nat := 4983230072969 + 3 ^ 40 * 2432359 * 2
def baseEnd_2432359 : Nat := 92516243799226230957503

theorem tailTrace_2432359 : CollatzResearch.WordTrace tailWord_2432359 prefixEnd_2432359 92516243799226230957503 := by
  unfold tailWord_2432359
  simp only [CollatzResearch.WordTrace]
  refine ⟨88715420994986231689524131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59143613996657487793016087 88715420994986231689524131)
  ·
    refine ⟨133073131492479347534286197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88715420994986231689524131 133073131492479347534286197)
    ·
      refine ⟨12475606077419938831339331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133073131492479347534286197 12475606077419938831339331)
      ·
        refine ⟨18713409116129908247008997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12475606077419938831339331 18713409116129908247008997)
        ·
          refine ⟨3508764209274357796314187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18713409116129908247008997 3508764209274357796314187)
          ·
            refine ⟨5263146313911536694471281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3508764209274357796314187 5263146313911536694471281)
            ·
              refine ⟨3947359735433652520853461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5263146313911536694471281 3947359735433652520853461)
              ·
                refine ⟨92516243799226230957503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3947359735433652520853461 92516243799226230957503)
                ·
                  rfl

theorem cell22_2432359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 7].length) (baseStart_2432359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2432359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2432359 prefixEnd_2432359 := by exact prefixLift 2432359
  have htrace : WordTrace (prefixWord ++ tailWord_2432359) baseStart_2432359 baseEnd_2432359 := by
    simpa [prefixWord, tailWord_2432359, baseEnd_2432359] using wordTrace_append hprefix tailTrace_2432359
  have hstable : (prefixWord ++ tailWord_2432359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432359).length < 2 ^ (prefixWord ++ tailWord_2432359).sum := by decide
  have hdescent : baseEnd_2432359 < baseStart_2432359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432451 : List Nat := [1, 1, 1, 3, 1, 1, 8, 1, 1, 4]
def baseStart_2432451 : Nat := 118140960795 + 2432451 * 2 ^ 59
def prefixEnd_2432451 : Nat := 4983230072969 + 3 ^ 40 * 2432451 * 2
def baseEnd_2432451 : Nat := 832677687673178505317245

theorem tailTrace_2432451 : CollatzResearch.WordTrace tailWord_2432451 prefixEnd_2432451 832677687673178505317245 := by
  unfold tailWord_2432451
  simp only [CollatzResearch.WordTrace]
  refine ⟨88718776510652931401873207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59145851007101954267915471 88718776510652931401873207)
  ·
    refine ⟨133078164765979397102809811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88718776510652931401873207 133078164765979397102809811)
    ·
      refine ⟨199617247148969095654214717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133078164765979397102809811 199617247148969095654214717)
      ·
        refine ⟨74856467680863410870330519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199617247148969095654214717 74856467680863410870330519)
        ·
          refine ⟨112284701521295116305495779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74856467680863410870330519 112284701521295116305495779)
          ·
            refine ⟨168427052281942674458243669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112284701521295116305495779 168427052281942674458243669)
            ·
              refine ⟨1973754518929015716307543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 168427052281942674458243669 1973754518929015716307543)
              ·
                refine ⟨2960631778393523574461315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1973754518929015716307543 2960631778393523574461315)
                ·
                  refine ⟨4440947667590285361691973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2960631778393523574461315 4440947667590285361691973)
                  ·
                    refine ⟨832677687673178505317245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4440947667590285361691973 832677687673178505317245)
                    ·
                      rfl

theorem cell22_2432451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 1, 4].length) (baseStart_2432451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2432451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2432451 prefixEnd_2432451 := by exact prefixLift 2432451
  have htrace : WordTrace (prefixWord ++ tailWord_2432451) baseStart_2432451 baseEnd_2432451 := by
    simpa [prefixWord, tailWord_2432451, baseEnd_2432451] using wordTrace_append hprefix tailTrace_2432451
  have hstable : (prefixWord ++ tailWord_2432451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432451).length < 2 ^ (prefixWord ++ tailWord_2432451).sum := by decide
  have hdescent : baseEnd_2432451 < baseStart_2432451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432464 : List Nat := [2, 1, 1, 1, 1, 2, 2, 5, 4, 3]
def baseStart_2432464 : Nat := 118140960795 + 2432464 * 2 ^ 59
def prefixEnd_2432464 : Nat := 4983230072969 + 3 ^ 40 * 2432464 * 2
def baseEnd_2432464 : Nat := 832682137838850804742205

theorem tailTrace_2432464 : CollatzResearch.WordTrace tailWord_2432464 prefixEnd_2432464 832682137838850804742205 := by
  unfold tailWord_2432464
  simp only [CollatzResearch.WordTrace]
  refine ⟨44359625329802917311048223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59146167106403889748064297 44359625329802917311048223)
  ·
    refine ⟨66539437994704375966572335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44359625329802917311048223 66539437994704375966572335)
    ·
      refine ⟨99809156992056563949858503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66539437994704375966572335 99809156992056563949858503)
      ·
        refine ⟨149713735488084845924787755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99809156992056563949858503 149713735488084845924787755)
        ·
          refine ⟨224570603232127268887181633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149713735488084845924787755 224570603232127268887181633)
          ·
            refine ⟨168427952424095451665386225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224570603232127268887181633 168427952424095451665386225)
            ·
              refine ⟨126320964318071588749039669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168427952424095451665386225 126320964318071588749039669)
              ·
                refine ⟨11842590404819211445222469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126320964318071588749039669 11842590404819211445222469)
                ·
                  refine ⟨2220485700903602145979213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11842590404819211445222469 2220485700903602145979213)
                  ·
                    refine ⟨832682137838850804742205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2220485700903602145979213 832682137838850804742205)
                    ·
                      rfl

theorem cell22_2432464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 4, 3].length) (baseStart_2432464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2432464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2432464 prefixEnd_2432464 := by exact prefixLift 2432464
  have htrace : WordTrace (prefixWord ++ tailWord_2432464) baseStart_2432464 baseEnd_2432464 := by
    simpa [prefixWord, tailWord_2432464, baseEnd_2432464] using wordTrace_append hprefix tailTrace_2432464
  have hstable : (prefixWord ++ tailWord_2432464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432464).length < 2 ^ (prefixWord ++ tailWord_2432464).sum := by decide
  have hdescent : baseEnd_2432464 < baseStart_2432464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432481 : List Nat := [1, 2, 3, 1, 2, 5, 1, 1, 1, 5]
def baseStart_2432481 : Nat := 118140960795 + 2432481 * 2 ^ 59
def prefixEnd_2432481 : Nat := 4983230072969 + 3 ^ 40 * 2432481 * 2
def baseEnd_2432481 : Nat := 832687957286268427067153

theorem tailTrace_2432481 : CollatzResearch.WordTrace tailWord_2432481 prefixEnd_2432481 832687957286268427067153 := by
  unfold tailWord_2432481
  simp only [CollatzResearch.WordTrace]
  refine ⟨88719870700544246525465297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59146580467029497683643531 88719870700544246525465297)
  ·
    refine ⟨66539903025408184894098973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88719870700544246525465297 66539903025408184894098973)
    ·
      refine ⟨24952463634528069335287115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66539903025408184894098973 24952463634528069335287115)
      ·
        refine ⟨37428695451792104002930673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24952463634528069335287115 37428695451792104002930673)
        ·
          refine ⟨28071521588844078002198005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37428695451792104002930673 28071521588844078002198005)
          ·
            refine ⟨2631705148954132312706063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28071521588844078002198005 2631705148954132312706063)
            ·
              refine ⟨3947557723431198469059095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2631705148954132312706063 3947557723431198469059095)
              ·
                refine ⟨5921336585146797703588643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3947557723431198469059095 5921336585146797703588643)
                ·
                  refine ⟨8882004877720196555382965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5921336585146797703588643 8882004877720196555382965)
                  ·
                    refine ⟨832687957286268427067153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8882004877720196555382965 832687957286268427067153)
                    ·
                      rfl

theorem cell22_2432481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_2432481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2432481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2432481 prefixEnd_2432481 := by exact prefixLift 2432481
  have htrace : WordTrace (prefixWord ++ tailWord_2432481) baseStart_2432481 baseEnd_2432481 := by
    simpa [prefixWord, tailWord_2432481, baseEnd_2432481] using wordTrace_append hprefix tailTrace_2432481
  have hstable : (prefixWord ++ tailWord_2432481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432481).length < 2 ^ (prefixWord ++ tailWord_2432481).sum := by decide
  have hdescent : baseEnd_2432481 < baseStart_2432481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432494 : List Nat := [4, 1, 2, 1, 2, 1, 3, 8]
def baseStart_2432494 : Nat := 118140960795 + 2432494 * 2 ^ 59
def prefixEnd_2432494 : Nat := 4983230072969 + 3 ^ 40 * 2432494 * 2
def baseEnd_2432494 : Nat := 92521378605771191832457

theorem tailTrace_2432494 : CollatzResearch.WordTrace tailWord_2432494 prefixEnd_2432494 92521378605771191832457 := by
  unfold tailWord_2432494
  simp only [CollatzResearch.WordTrace]
  refine ⟨11090043106187143718211067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59146896566331433163792357 11090043106187143718211067)
  ·
    refine ⟨16635064659280715577316601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11090043106187143718211067 16635064659280715577316601)
    ·
      refine ⟨12476298494460536682987451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16635064659280715577316601 12476298494460536682987451)
      ·
        refine ⟨18714447741690805024481177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12476298494460536682987451 18714447741690805024481177)
        ·
          refine ⟨14035835806268103768360883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18714447741690805024481177 14035835806268103768360883)
          ·
            refine ⟨21053753709402155652541325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14035835806268103768360883 21053753709402155652541325)
            ·
              refine ⟨7895157641025808369702997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21053753709402155652541325 7895157641025808369702997)
              ·
                refine ⟨92521378605771191832457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7895157641025808369702997 92521378605771191832457)
                ·
                  rfl

theorem cell22_2432494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 8].length) (baseStart_2432494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2432494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2432494 prefixEnd_2432494 := by exact prefixLift 2432494
  have htrace : WordTrace (prefixWord ++ tailWord_2432494) baseStart_2432494 baseEnd_2432494 := by
    simpa [prefixWord, tailWord_2432494, baseEnd_2432494] using wordTrace_append hprefix tailTrace_2432494
  have hstable : (prefixWord ++ tailWord_2432494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432494).length < 2 ^ (prefixWord ++ tailWord_2432494).sum := by decide
  have hdescent : baseEnd_2432494 < baseStart_2432494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432573 : List Nat := [1, 4, 1, 3, 3, 1, 2, 2, 5]
def baseStart_2432573 : Nat := 118140960795 + 2432573 * 2 ^ 59
def prefixEnd_2432573 : Nat := 4983230072969 + 3 ^ 40 * 2432573 * 2
def baseEnd_2432573 : Nat := 277573150255470284588957

theorem tailTrace_2432573 : CollatzResearch.WordTrace tailWord_2432573 prefixEnd_2432573 277573150255470284588957 := by
  unfold tailWord_2432573
  simp only [CollatzResearch.WordTrace]
  refine ⟨88723226216210946237814373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59148817477473964158542915 88723226216210946237814373)
  ·
    refine ⟨16635604915539552419590195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88723226216210946237814373 16635604915539552419590195)
    ·
      refine ⟨24953407373309328629385293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16635604915539552419590195 24953407373309328629385293)
      ·
        refine ⟨9357527764990998236019485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24953407373309328629385293 9357527764990998236019485)
        ·
          refine ⟨3509072911871624338507307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9357527764990998236019485 3509072911871624338507307)
          ·
            refine ⟨5263609367807436507760961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3509072911871624338507307 5263609367807436507760961)
            ·
              refine ⟨3947707025855577380820721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5263609367807436507760961 3947707025855577380820721)
              ·
                refine ⟨2960780269391683035615541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3947707025855577380820721 2960780269391683035615541)
                ·
                  refine ⟨277573150255470284588957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2960780269391683035615541 277573150255470284588957)
                  ·
                    rfl

theorem cell22_2432573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_2432573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2432573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2432573 prefixEnd_2432573 := by exact prefixLift 2432573
  have htrace : WordTrace (prefixWord ++ tailWord_2432573) baseStart_2432573 baseEnd_2432573 := by
    simpa [prefixWord, tailWord_2432573, baseEnd_2432573] using wordTrace_append hprefix tailTrace_2432573
  have hstable : (prefixWord ++ tailWord_2432573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432573).length < 2 ^ (prefixWord ++ tailWord_2432573).sum := by decide
  have hdescent : baseEnd_2432573 < baseStart_2432573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432618 : List Nat := [3, 1, 3, 2, 1, 2, 1, 5, 4]
def baseStart_2432618 : Nat := 118140960795 + 2432618 * 2 ^ 59
def prefixEnd_2432618 : Nat := 4983230072969 + 3 ^ 40 * 2432618 * 2
def baseEnd_2432618 : Nat := 277578285062015245463911

theorem tailTrace_2432618 : CollatzResearch.WordTrace tailWord_2432618 prefixEnd_2432618 277578285062015245463911 := by
  unfold tailWord_2432618
  simp only [CollatzResearch.WordTrace]
  refine ⟨22181216875261979730800627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59149911667365279282135005 22181216875261979730800627)
  ·
    refine ⟨33271825312892969596200941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22181216875261979730800627 33271825312892969596200941)
    ·
      refine ⟨12476934492334863598575353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33271825312892969596200941 12476934492334863598575353)
      ·
        refine ⟨9357700869251147698931515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12476934492334863598575353 9357700869251147698931515)
        ·
          refine ⟨14036551303876721548397273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9357700869251147698931515 14036551303876721548397273)
          ·
            refine ⟨10527413477907541161297955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14036551303876721548397273 10527413477907541161297955)
            ·
              refine ⟨15791120216861311741946933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10527413477907541161297955 15791120216861311741946933)
              ·
                refine ⟨1480417520330747975807525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15791120216861311741946933 1480417520330747975807525)
                ·
                  refine ⟨277578285062015245463911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1480417520330747975807525 277578285062015245463911)
                  ·
                    rfl

theorem cell22_2432618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 5, 4].length) (baseStart_2432618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2432618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2432618 prefixEnd_2432618 := by exact prefixLift 2432618
  have htrace : WordTrace (prefixWord ++ tailWord_2432618) baseStart_2432618 baseEnd_2432618 := by
    simpa [prefixWord, tailWord_2432618, baseEnd_2432618] using wordTrace_append hprefix tailTrace_2432618
  have hstable : (prefixWord ++ tailWord_2432618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432618).length < 2 ^ (prefixWord ++ tailWord_2432618).sum := by decide
  have hdescent : baseEnd_2432618 < baseStart_2432618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432663 : List Nat := [1, 1, 3, 3, 2, 4, 2, 6]
def baseStart_2432663 : Nat := 118140960795 + 2432663 * 2 ^ 59
def prefixEnd_2432663 : Nat := 4983230072969 + 3 ^ 40 * 2432663 * 2
def baseEnd_2432663 : Nat := 92527806622853402112955

theorem tailTrace_2432663 : CollatzResearch.WordTrace tailWord_2432663 prefixEnd_2432663 92527806622853402112955 := by
  unfold tailWord_2432663
  simp only [CollatzResearch.WordTrace]
  refine ⟨88726508785884891608590643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59151005857256594405727095 88726508785884891608590643)
  ·
    refine ⟨133089763178827337412885965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88726508785884891608590643 133089763178827337412885965)
    ·
      refine ⟨49908661192060251529832237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133089763178827337412885965 49908661192060251529832237)
      ·
        refine ⟨18715747947022594323687089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49908661192060251529832237 18715747947022594323687089)
        ·
          refine ⟨14036810960266945742765317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18715747947022594323687089 14036810960266945742765317)
          ·
            refine ⟨2631902055050052326768497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14036810960266945742765317 2631902055050052326768497)
            ·
              refine ⟨1973926541287539245076373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2631902055050052326768497 1973926541287539245076373)
              ·
                refine ⟨92527806622853402112955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1973926541287539245076373 92527806622853402112955)
                ·
                  rfl

theorem cell22_2432663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 6].length) (baseStart_2432663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2432663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2432663 prefixEnd_2432663 := by exact prefixLift 2432663
  have htrace : WordTrace (prefixWord ++ tailWord_2432663) baseStart_2432663 baseEnd_2432663 := by
    simpa [prefixWord, tailWord_2432663, baseEnd_2432663] using wordTrace_append hprefix tailTrace_2432663
  have hstable : (prefixWord ++ tailWord_2432663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432663).length < 2 ^ (prefixWord ++ tailWord_2432663).sum := by decide
  have hdescent : baseEnd_2432663 < baseStart_2432663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432691 : List Nat := [1, 1, 1, 2, 3, 3, 2, 4, 5]
def baseStart_2432691 : Nat := 118140960795 + 2432691 * 2 ^ 59
def prefixEnd_2432691 : Nat := 4983230072969 + 3 ^ 40 * 2432691 * 2
def baseEnd_2432691 : Nat := 277586614859299293105503

theorem tailTrace_2432691 : CollatzResearch.WordTrace tailWord_2432691 prefixEnd_2432691 277586614859299293105503 := by
  unfold tailWord_2432691
  simp only [CollatzResearch.WordTrace]
  refine ⟨88727530029783452390609927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59151686686522301593739951 88727530029783452390609927)
  ·
    refine ⟨133091295044675178585914891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88727530029783452390609927 133091295044675178585914891)
    ·
      refine ⟨199636942567012767878872337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133091295044675178585914891 199636942567012767878872337)
      ·
        refine ⟨149727706925259575909154253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199636942567012767878872337 149727706925259575909154253)
        ·
          refine ⟨56147890096972340965932845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149727706925259575909154253 56147890096972340965932845)
          ·
            refine ⟨21055458786364627862224817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56147890096972340965932845 21055458786364627862224817)
            ·
              refine ⟨15791594089773470896668613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21055458786364627862224817 15791594089773470896668613)
              ·
                refine ⟨2960923891832525793125365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15791594089773470896668613 2960923891832525793125365)
                ·
                  refine ⟨277586614859299293105503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2960923891832525793125365 277586614859299293105503)
                  ·
                    rfl

theorem cell22_2432691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 5].length) (baseStart_2432691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2432691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2432691 prefixEnd_2432691 := by exact prefixLift 2432691
  have htrace : WordTrace (prefixWord ++ tailWord_2432691) baseStart_2432691 baseEnd_2432691 := by
    simpa [prefixWord, tailWord_2432691, baseEnd_2432691] using wordTrace_append hprefix tailTrace_2432691
  have hstable : (prefixWord ++ tailWord_2432691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432691).length < 2 ^ (prefixWord ++ tailWord_2432691).sum := by decide
  have hdescent : baseEnd_2432691 < baseStart_2432691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432695 : List Nat := [1, 1, 3, 1, 5, 3, 1, 1, 3, 3]
def baseStart_2432695 : Nat := 118140960795 + 2432695 * 2 ^ 59
def prefixEnd_2432695 : Nat := 4983230072969 + 3 ^ 40 * 2432695 * 2
def baseEnd_2432695 : Nat := 832761213859643202216497

theorem tailTrace_2432695 : CollatzResearch.WordTrace tailWord_2432695 prefixEnd_2432695 832761213859643202216497 := by
  unfold tailWord_2432695
  simp only [CollatzResearch.WordTrace]
  refine ⟨88727675921768961073755539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59151783947845974049170359 88727675921768961073755539)
  ·
    refine ⟨133091513882653441610633309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88727675921768961073755539 133091513882653441610633309)
    ·
      refine ⟨49909317705995040603987491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133091513882653441610633309 49909317705995040603987491)
      ·
        refine ⟨74863976558992560905981237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49909317705995040603987491 74863976558992560905981237)
        ·
          refine ⟨7018497802405552584935741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74863976558992560905981237 7018497802405552584935741)
          ·
            refine ⟨2631936675902082219350903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7018497802405552584935741 2631936675902082219350903)
            ·
              refine ⟨3947905013853123329026355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2631936675902082219350903 3947905013853123329026355)
              ·
                refine ⟨5921857520779684993539533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3947905013853123329026355 5921857520779684993539533)
                ·
                  refine ⟨2220696570292381872577325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5921857520779684993539533 2220696570292381872577325)
                  ·
                    refine ⟨832761213859643202216497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2220696570292381872577325 832761213859643202216497)
                    ·
                      rfl

theorem cell22_2432695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 3, 3].length) (baseStart_2432695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2432695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2432695 prefixEnd_2432695 := by exact prefixLift 2432695
  have htrace : WordTrace (prefixWord ++ tailWord_2432695) baseStart_2432695 baseEnd_2432695 := by
    simpa [prefixWord, tailWord_2432695, baseEnd_2432695] using wordTrace_append hprefix tailTrace_2432695
  have hstable : (prefixWord ++ tailWord_2432695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432695).length < 2 ^ (prefixWord ++ tailWord_2432695).sum := by decide
  have hdescent : baseEnd_2432695 < baseStart_2432695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432708 : List Nat := [2, 3, 3, 1, 1, 1, 3, 3, 5]
def baseStart_2432708 : Nat := 118140960795 + 2432708 * 2 ^ 59
def prefixEnd_2432708 : Nat := 4983230072969 + 3 ^ 40 * 2432708 * 2
def baseEnd_2432708 : Nat := 277588554675105167213819

theorem tailTrace_2432708 : CollatzResearch.WordTrace tailWord_2432708 prefixEnd_2432708 277588554675105167213819 := by
  unfold tailWord_2432708
  simp only [CollatzResearch.WordTrace]
  refine ⟨44364075035360932146989389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59152100047147909529319185 44364075035360932146989389)
  ·
    refine ⟨16636528138260349555121021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44364075035360932146989389 16636528138260349555121021)
    ·
      refine ⟨6238698051847631083170383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16636528138260349555121021 6238698051847631083170383)
      ·
        refine ⟨9358047077771446624755575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6238698051847631083170383 9358047077771446624755575)
        ·
          refine ⟨14037070616657169937133363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9358047077771446624755575 14037070616657169937133363)
          ·
            refine ⟨21055605924985754905700045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14037070616657169937133363 21055605924985754905700045)
            ·
              refine ⟨7895852221869658089637517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21055605924985754905700045 7895852221869658089637517)
              ·
                refine ⟨2960944583201121783614069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7895852221869658089637517 2960944583201121783614069)
                ·
                  refine ⟨277588554675105167213819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2960944583201121783614069 277588554675105167213819)
                  ·
                    rfl

theorem cell22_2432708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_2432708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2432708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2432708 prefixEnd_2432708 := by exact prefixLift 2432708
  have htrace : WordTrace (prefixWord ++ tailWord_2432708) baseStart_2432708 baseEnd_2432708 := by
    simpa [prefixWord, tailWord_2432708, baseEnd_2432708] using wordTrace_append hprefix tailTrace_2432708
  have hstable : (prefixWord ++ tailWord_2432708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432708).length < 2 ^ (prefixWord ++ tailWord_2432708).sum := by decide
  have hdescent : baseEnd_2432708 < baseStart_2432708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432751 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 3, 5]
def baseStart_2432751 : Nat := 118140960795 + 2432751 * 2 ^ 59
def prefixEnd_2432751 : Nat := 4983230072969 + 3 ^ 40 * 2432751 * 2
def baseEnd_2432751 : Nat := 832780383804077722816325

theorem tailTrace_2432751 : CollatzResearch.WordTrace tailWord_2432751 prefixEnd_2432751 832780383804077722816325 := by
  unfold tailWord_2432751
  simp only [CollatzResearch.WordTrace]
  refine ⟨88729718409566082637794107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59153145606377388425196071 88729718409566082637794107)
  ·
    refine ⟨133094577614349123956691161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88729718409566082637794107 133094577614349123956691161)
    ·
      refine ⟨99820933210761842967518371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133094577614349123956691161 99820933210761842967518371)
      ·
        refine ⟨149731399816142764451277557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99820933210761842967518371 149731399816142764451277557)
        ·
          refine ⟨14037318732763384167307271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 149731399816142764451277557 14037318732763384167307271)
          ·
            refine ⟨21055978099145076250960907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14037318732763384167307271 21055978099145076250960907)
            ·
              refine ⟨31583967148717614376441361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21055978099145076250960907 31583967148717614376441361)
              ·
                refine ⟨23687975361538210782331021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31583967148717614376441361 23687975361538210782331021)
                ·
                  refine ⟨8882990760576829043374133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23687975361538210782331021 8882990760576829043374133)
                  ·
                    refine ⟨832780383804077722816325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8882990760576829043374133 832780383804077722816325)
                    ·
                      rfl

theorem cell22_2432751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 5].length) (baseStart_2432751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2432751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2432751 prefixEnd_2432751 := by exact prefixLift 2432751
  have htrace : WordTrace (prefixWord ++ tailWord_2432751) baseStart_2432751 baseEnd_2432751 := by
    simpa [prefixWord, tailWord_2432751, baseEnd_2432751] using wordTrace_append hprefix tailTrace_2432751
  have hstable : (prefixWord ++ tailWord_2432751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432751).length < 2 ^ (prefixWord ++ tailWord_2432751).sum := by decide
  have hdescent : baseEnd_2432751 < baseStart_2432751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432864 : List Nat := [2, 1, 1, 3, 3, 3, 3, 2, 1, 3]
def baseStart_2432864 : Nat := 118140960795 + 2432864 * 2 ^ 59
def prefixEnd_2432864 : Nat := 4983230072969 + 3 ^ 40 * 2432864 * 2
def baseEnd_2432864 : Nat := 832819066013383094740979

theorem tailTrace_2432864 : CollatzResearch.WordTrace tailWord_2432864 prefixEnd_2432864 832819066013383094740979 := by
  unfold tailWord_2432864
  simp only [CollatzResearch.WordTrace]
  refine ⟨44366919929078351468328823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59155893238771135291105097 44366919929078351468328823)
  ·
    refine ⟨66550379893617527202493235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44366919929078351468328823 66550379893617527202493235)
    ·
      refine ⟨99825569840426290803739853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66550379893617527202493235 99825569840426290803739853)
      ·
        refine ⟨37434588690159859051402445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99825569840426290803739853 37434588690159859051402445)
        ·
          refine ⟨14037970758809947144275917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37434588690159859051402445 14037970758809947144275917)
          ·
            refine ⟨5264239034553730179103469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14037970758809947144275917 5264239034553730179103469)
            ·
              refine ⟨1974089637957648817163801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5264239034553730179103469 1974089637957648817163801)
              ·
                refine ⟨1480567228468236612872851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1974089637957648817163801 1480567228468236612872851)
                ·
                  refine ⟨2220850842702354919309277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1480567228468236612872851 2220850842702354919309277)
                  ·
                    refine ⟨832819066013383094740979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2220850842702354919309277 832819066013383094740979)
                    ·
                      rfl

theorem cell22_2432864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 2, 1, 3].length) (baseStart_2432864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2432864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2432864 prefixEnd_2432864 := by exact prefixLift 2432864
  have htrace : WordTrace (prefixWord ++ tailWord_2432864) baseStart_2432864 baseEnd_2432864 := by
    simpa [prefixWord, tailWord_2432864, baseEnd_2432864] using wordTrace_append hprefix tailTrace_2432864
  have hstable : (prefixWord ++ tailWord_2432864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432864).length < 2 ^ (prefixWord ++ tailWord_2432864).sum := by decide
  have hdescent : baseEnd_2432864 < baseStart_2432864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432890 : List Nat := [3, 1, 1, 1, 1, 1, 7, 2, 1, 4]
def baseStart_2432890 : Nat := 118140960795 + 2432890 * 2 ^ 59
def prefixEnd_2432890 : Nat := 4983230072969 + 3 ^ 40 * 2432890 * 2
def baseEnd_2432890 : Nat := 832827966344727693590899

theorem tailTrace_2432890 : CollatzResearch.WordTrace tailWord_2432890 prefixEnd_2432890 832827966344727693590899 := by
  unfold tailWord_2432890
  simp only [CollatzResearch.WordTrace]
  refine ⟨22183697039015627344276031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59156525437375006251402749 22183697039015627344276031)
  ·
    refine ⟨33275545558523441016414047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22183697039015627344276031 33275545558523441016414047)
    ·
      refine ⟨49913318337785161524621071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33275545558523441016414047 49913318337785161524621071)
      ·
        refine ⟨74869977506677742286931607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49913318337785161524621071 74869977506677742286931607)
        ·
          refine ⟨112304966260016613430397411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74869977506677742286931607 112304966260016613430397411)
          ·
            refine ⟨168457449390024920145596117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112304966260016613430397411 168457449390024920145596117)
            ·
              refine ⟨3948221470078709065912409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 168457449390024920145596117 3948221470078709065912409)
              ·
                refine ⟨2961166102559031799434307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3948221470078709065912409 2961166102559031799434307)
                ·
                  refine ⟨4441749153838547699151461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2961166102559031799434307 4441749153838547699151461)
                  ·
                    refine ⟨832827966344727693590899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4441749153838547699151461 832827966344727693590899)
                    ·
                      rfl

theorem cell22_2432890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_2432890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2432890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2432890 prefixEnd_2432890 := by exact prefixLift 2432890
  have htrace : WordTrace (prefixWord ++ tailWord_2432890) baseStart_2432890 baseEnd_2432890 := by
    simpa [prefixWord, tailWord_2432890, baseEnd_2432890] using wordTrace_append hprefix tailTrace_2432890
  have hstable : (prefixWord ++ tailWord_2432890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432890).length < 2 ^ (prefixWord ++ tailWord_2432890).sum := by decide
  have hdescent : baseEnd_2432890 < baseStart_2432890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432905 : List Nat := [1, 2, 1, 1, 5, 1, 2, 5, 4]
def baseStart_2432905 : Nat := 118140960795 + 2432905 * 2 ^ 59
def prefixEnd_2432905 : Nat := 4983230072969 + 3 ^ 40 * 2432905 * 2
def baseEnd_2432905 : Nat := 277611033717090884821951

theorem tailTrace_2432905 : CollatzResearch.WordTrace tailWord_2432905 prefixEnd_2432905 277611033717090884821951 := by
  unfold tailWord_2432905
  simp only [CollatzResearch.WordTrace]
  refine ⟨88735335251008166938900169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59156890167338777959266779 88735335251008166938900169)
  ·
    refine ⟨66551501438256125204175127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88735335251008166938900169 66551501438256125204175127)
    ·
      refine ⟨99827252157384187806262691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66551501438256125204175127 99827252157384187806262691)
      ·
        refine ⟨149740878236076281709394037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99827252157384187806262691 149740878236076281709394037)
        ·
          refine ⟨14038207334632151410255691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 149740878236076281709394037 14038207334632151410255691)
          ·
            refine ⟨21057311001948227115383537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14038207334632151410255691 21057311001948227115383537)
            ·
              refine ⟨15792983251461170336537653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21057311001948227115383537 15792983251461170336537653)
              ·
                refine ⟨1480592179824484719050405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15792983251461170336537653 1480592179824484719050405)
                ·
                  refine ⟨277611033717090884821951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1480592179824484719050405 277611033717090884821951)
                  ·
                    rfl

theorem cell22_2432905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 5, 4].length) (baseStart_2432905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2432905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2432905 prefixEnd_2432905 := by exact prefixLift 2432905
  have htrace : WordTrace (prefixWord ++ tailWord_2432905) baseStart_2432905 baseEnd_2432905 := by
    simpa [prefixWord, tailWord_2432905, baseEnd_2432905] using wordTrace_append hprefix tailTrace_2432905
  have hstable : (prefixWord ++ tailWord_2432905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432905).length < 2 ^ (prefixWord ++ tailWord_2432905).sum := by decide
  have hdescent : baseEnd_2432905 < baseStart_2432905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432922 : List Nat := [3, 1, 1, 4, 2, 2, 1, 4, 4]
def baseStart_2432922 : Nat := 118140960795 + 2432922 * 2 ^ 59
def prefixEnd_2432922 : Nat := 4983230072969 + 3 ^ 40 * 2432922 * 2
def baseEnd_2432922 : Nat := 277612973532896758930267

theorem tailTrace_2432922 : CollatzResearch.WordTrace tailWord_2432922 prefixEnd_2432922 277612973532896758930267 := by
  unfold tailWord_2432922
  simp only [CollatzResearch.WordTrace]
  refine ⟨22183988822986644710567255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59157303527964385894846013 22183988822986644710567255)
  ·
    refine ⟨33275983234479967065850883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22183988822986644710567255 33275983234479967065850883)
    ·
      refine ⟨49913974851719950598776325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33275983234479967065850883 49913974851719950598776325)
      ·
        refine ⟨9358870284697490737270561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49913974851719950598776325 9358870284697490737270561)
        ·
          refine ⟨7019152713523118052952921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9358870284697490737270561 7019152713523118052952921)
          ·
            refine ⟨5264364535142338539714691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7019152713523118052952921 5264364535142338539714691)
            ·
              refine ⟨7896546802713507809572037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5264364535142338539714691 7896546802713507809572037)
              ·
                refine ⟨1480602525508782714294757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7896546802713507809572037 1480602525508782714294757)
                ·
                  refine ⟨277612973532896758930267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1480602525508782714294757 277612973532896758930267)
                  ·
                    rfl

theorem cell22_2432922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 4, 4].length) (baseStart_2432922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2432922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2432922 prefixEnd_2432922 := by exact prefixLift 2432922
  have htrace : WordTrace (prefixWord ++ tailWord_2432922) baseStart_2432922 baseEnd_2432922 := by
    simpa [prefixWord, tailWord_2432922, baseEnd_2432922] using wordTrace_append hprefix tailTrace_2432922
  have hstable : (prefixWord ++ tailWord_2432922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432922).length < 2 ^ (prefixWord ++ tailWord_2432922).sum := by decide
  have hdescent : baseEnd_2432922 < baseStart_2432922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432988 : List Nat := [2, 2, 6, 1, 2, 1, 1, 1, 1, 5]
def baseStart_2432988 : Nat := 118140960795 + 2432988 * 2 ^ 59
def prefixEnd_2432988 : Nat := 4983230072969 + 3 ^ 40 * 2432988 * 2
def baseEnd_2432988 : Nat := 832861513747488104640599

theorem tailTrace_2432988 : CollatzResearch.WordTrace tailWord_2432988 prefixEnd_2432988 832861513747488104640599 := by
  unfold tailWord_2432988
  simp only [CollatzResearch.WordTrace]
  refine ⟨44369181254853736057085809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59158908339804981409447745 44369181254853736057085809)
  ·
    refine ⟨33276885941140302042814357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44369181254853736057085809 33276885941140302042814357)
    ·
      refine ⟨1559854028490951658256923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33276885941140302042814357 1559854028490951658256923)
      ·
        refine ⟨2339781042736427487385385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1559854028490951658256923 2339781042736427487385385)
        ·
          refine ⟨1754835782052320615539039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2339781042736427487385385 1754835782052320615539039)
          ·
            refine ⟨2632253673078480923308559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1754835782052320615539039 2632253673078480923308559)
            ·
              refine ⟨3948380509617721384962839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2632253673078480923308559 3948380509617721384962839)
              ·
                refine ⟨5922570764426582077444259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3948380509617721384962839 5922570764426582077444259)
                ·
                  refine ⟨8883856146639873116166389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5922570764426582077444259 8883856146639873116166389)
                  ·
                    refine ⟨832861513747488104640599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8883856146639873116166389 832861513747488104640599)
                    ·
                      rfl

theorem cell22_2432988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_2432988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2432988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2432988 prefixEnd_2432988 := by exact prefixLift 2432988
  have htrace : WordTrace (prefixWord ++ tailWord_2432988) baseStart_2432988 baseEnd_2432988 := by
    simpa [prefixWord, tailWord_2432988, baseEnd_2432988] using wordTrace_append hprefix tailTrace_2432988
  have hstable : (prefixWord ++ tailWord_2432988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432988).length < 2 ^ (prefixWord ++ tailWord_2432988).sum := by decide
  have hdescent : baseEnd_2432988 < baseStart_2432988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433023 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 8]
def baseStart_2433023 : Nat := 118140960795 + 2433023 * 2 ^ 59
def prefixEnd_2433023 : Nat := 4983230072969 + 3 ^ 40 * 2433023 * 2
def baseEnd_2433023 : Nat := 277624498320919893338497

theorem tailTrace_2433023 : CollatzResearch.WordTrace tailWord_2433023 prefixEnd_2433023 277624498320919893338497 := by
  unfold tailWord_2433023
  simp only [CollatzResearch.WordTrace]
  refine ⟨88739639064580673091695723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59159759376387115394463815 88739639064580673091695723)
  ·
    refine ⟨133109458596871009637543585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88739639064580673091695723 133109458596871009637543585)
    ·
      refine ⟨99832093947653257228157689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133109458596871009637543585 99832093947653257228157689)
      ·
        refine ⟨74874070460739942921118267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99832093947653257228157689 74874070460739942921118267)
        ·
          refine ⟨112311105691109914381677401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74874070460739942921118267 112311105691109914381677401)
          ·
            refine ⟨84233329268332435786258051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112311105691109914381677401 84233329268332435786258051)
            ·
              refine ⟨126349993902498653679387077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84233329268332435786258051 126349993902498653679387077)
              ·
                refine ⟨23690623856718497564885077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126349993902498653679387077 23690623856718497564885077)
                ·
                  refine ⟨277624498320919893338497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23690623856718497564885077 277624498320919893338497)
                  ·
                    rfl

theorem cell22_2433023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 8].length) (baseStart_2433023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2433023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2433023 prefixEnd_2433023 := by exact prefixLift 2433023
  have htrace : WordTrace (prefixWord ++ tailWord_2433023) baseStart_2433023 baseEnd_2433023 := by
    simpa [prefixWord, tailWord_2433023, baseEnd_2433023] using wordTrace_append hprefix tailTrace_2433023
  have hstable : (prefixWord ++ tailWord_2433023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433023).length < 2 ^ (prefixWord ++ tailWord_2433023).sum := by decide
  have hdescent : baseEnd_2433023 < baseStart_2433023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433055 : List Nat := [1, 1, 2, 4, 1, 2, 2, 3, 1, 5]
def baseStart_2433055 : Nat := 118140960795 + 2433055 * 2 ^ 59
def prefixEnd_2433055 : Nat := 4983230072969 + 3 ^ 40 * 2433055 * 2
def baseEnd_2433055 : Nat := 832884449216722263215393

theorem tailTrace_2433055 : CollatzResearch.WordTrace tailWord_2433055 prefixEnd_2433055 832884449216722263215393 := by
  unfold tailWord_2433055
  simp only [CollatzResearch.WordTrace]
  refine ⟨88740806200464742556860619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59160537466976495037907079 88740806200464742556860619)
  ·
    refine ⟨133111209300697113835290929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88740806200464742556860619 133111209300697113835290929)
    ·
      refine ⟨99833406975522835376468197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133111209300697113835290929 99833406975522835376468197)
      ·
        refine ⟨18718763807910531633087787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99833406975522835376468197 18718763807910531633087787)
        ·
          refine ⟨28078145711865797449631681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18718763807910531633087787 28078145711865797449631681)
          ·
            refine ⟨21058609283899348087223761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28078145711865797449631681 21058609283899348087223761)
            ·
              refine ⟨15793956962924511065417821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21058609283899348087223761 15793956962924511065417821)
              ·
                refine ⟨5922733861096691649531683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15793956962924511065417821 5922733861096691649531683)
                ·
                  refine ⟨8884100791645037474297525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5922733861096691649531683 8884100791645037474297525)
                  ·
                    refine ⟨832884449216722263215393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8884100791645037474297525 832884449216722263215393)
                    ·
                      rfl

theorem cell22_2433055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 5].length) (baseStart_2433055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2433055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2433055 prefixEnd_2433055 := by exact prefixLift 2433055
  have htrace : WordTrace (prefixWord ++ tailWord_2433055) baseStart_2433055 baseEnd_2433055 := by
    simpa [prefixWord, tailWord_2433055, baseEnd_2433055] using wordTrace_append hprefix tailTrace_2433055
  have hstable : (prefixWord ++ tailWord_2433055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433055).length < 2 ^ (prefixWord ++ tailWord_2433055).sum := by decide
  have hdescent : baseEnd_2433055 < baseStart_2433055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433089 : List Nat := [1, 2, 5, 1, 2, 1, 1, 4, 2, 3]
def baseStart_2433089 : Nat := 118140960795 + 2433089 * 2 ^ 59
def prefixEnd_2433089 : Nat := 4983230072969 + 3 ^ 40 * 2433089 * 2
def baseEnd_2433089 : Nat := 832896088111557507865289

theorem tailTrace_2433089 : CollatzResearch.WordTrace tailWord_2433089 prefixEnd_2433089 832896088111557507865289 := by
  unfold tailWord_2433089
  simp only [CollatzResearch.WordTrace]
  refine ⟨88742046282341566363598321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59161364188227710909065547 88742046282341566363598321)
  ·
    refine ⟨66556534711756174772698741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88742046282341566363598321 66556534711756174772698741)
    ·
      refine ⟨6239675129227141384940507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66556534711756174772698741 6239675129227141384940507)
      ·
        refine ⟨9359512693840712077410761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6239675129227141384940507 9359512693840712077410761)
        ·
          refine ⟨7019634520380534058058071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9359512693840712077410761 7019634520380534058058071)
          ·
            refine ⟨10529451780570801087087107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7019634520380534058058071 10529451780570801087087107)
            ·
              refine ⟨15794177670856201630630661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10529451780570801087087107 15794177670856201630630661)
              ·
                refine ⟨2961408313285537805743249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15794177670856201630630661 2961408313285537805743249)
                ·
                  refine ⟨2221056234964153354307437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2961408313285537805743249 2221056234964153354307437)
                  ·
                    refine ⟨832896088111557507865289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2221056234964153354307437 832896088111557507865289)
                    ·
                      rfl

theorem cell22_2433089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_2433089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2433089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2433089 prefixEnd_2433089 := by exact prefixLift 2433089
  have htrace : WordTrace (prefixWord ++ tailWord_2433089) baseStart_2433089 baseEnd_2433089 := by
    simpa [prefixWord, tailWord_2433089, baseEnd_2433089] using wordTrace_append hprefix tailTrace_2433089
  have hstable : (prefixWord ++ tailWord_2433089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433089).length < 2 ^ (prefixWord ++ tailWord_2433089).sum := by decide
  have hdescent : baseEnd_2433089 < baseStart_2433089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433102 : List Nat := [4, 1, 1, 1, 1, 6, 1, 7]
def baseStart_2433102 : Nat := 118140960795 + 2433102 * 2 ^ 59
def prefixEnd_2433102 : Nat := 4983230072969 + 3 ^ 40 * 2433102 * 2
def baseEnd_2433102 : Nat := 92544504253025534143361

theorem tailTrace_2433102 : CollatzResearch.WordTrace tailWord_2433102 prefixEnd_2433102 92544504253025534143361 := by
  unfold tailWord_2433102
  simp only [CollatzResearch.WordTrace]
  refine ⟨11092815053911808697977695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59161680287529646389214373 11092815053911808697977695)
  ·
    refine ⟨16639222580867713046966543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11092815053911808697977695 16639222580867713046966543)
    ·
      refine ⟨24958833871301569570449815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16639222580867713046966543 24958833871301569570449815)
      ·
        refine ⟨37438250806952354355674723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24958833871301569570449815 37438250806952354355674723)
        ·
          refine ⟨56157376210428531533512085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37438250806952354355674723 56157376210428531533512085)
          ·
            refine ⟨2632377009863837415633379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 56157376210428531533512085 2632377009863837415633379)
            ·
              refine ⟨3948565514795756123450069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2632377009863837415633379 3948565514795756123450069)
              ·
                refine ⟨92544504253025534143361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3948565514795756123450069 92544504253025534143361)
                ·
                  rfl

theorem cell22_2433102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 7].length) (baseStart_2433102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2433102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2433102 prefixEnd_2433102 := by exact prefixLift 2433102
  have htrace : WordTrace (prefixWord ++ tailWord_2433102) baseStart_2433102 baseEnd_2433102 := by
    simpa [prefixWord, tailWord_2433102, baseEnd_2433102] using wordTrace_append hprefix tailTrace_2433102
  have hstable : (prefixWord ++ tailWord_2433102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433102).length < 2 ^ (prefixWord ++ tailWord_2433102).sum := by decide
  have hdescent : baseEnd_2433102 < baseStart_2433102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433162 : List Nat := [3, 1, 2, 3, 1, 2, 2, 1, 2, 5]
def baseStart_2433162 : Nat := 118140960795 + 2433162 * 2 ^ 59
def prefixEnd_2433162 : Nat := 4983230072969 + 3 ^ 40 * 2433162 * 2
def baseEnd_2433162 : Nat := 832921077503409650790065

theorem tailTrace_2433162 : CollatzResearch.WordTrace tailWord_2433162 prefixEnd_2433162 832921077503409650790065 := by
  unfold tailWord_2433162
  simp only [CollatzResearch.WordTrace]
  refine ⟨22186177202769274957751435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59163139207384733220670493 22186177202769274957751435)
  ·
    refine ⟨33279265804153912436627153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22186177202769274957751435 33279265804153912436627153)
    ·
      refine ⟨24959449353115434327470365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33279265804153912436627153 24959449353115434327470365)
      ·
        refine ⟨9359793507418287872801387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24959449353115434327470365 9359793507418287872801387)
        ·
          refine ⟨14039690261127431809202081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9359793507418287872801387 14039690261127431809202081)
          ·
            refine ⟨10529767695845573856901561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14039690261127431809202081 10529767695845573856901561)
            ·
              refine ⟨7897325771884180392676171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10529767695845573856901561 7897325771884180392676171)
              ·
                refine ⟨11845988657826270589014257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7897325771884180392676171 11845988657826270589014257)
                ·
                  refine ⟨8884491493369702941760693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11845988657826270589014257 8884491493369702941760693)
                  ·
                    refine ⟨832921077503409650790065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8884491493369702941760693 832921077503409650790065)
                    ·
                      rfl

theorem cell22_2433162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_2433162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2433162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2433162 prefixEnd_2433162 := by exact prefixLift 2433162
  have htrace : WordTrace (prefixWord ++ tailWord_2433162) baseStart_2433162 baseEnd_2433162 := by
    simpa [prefixWord, tailWord_2433162, baseEnd_2433162] using wordTrace_append hprefix tailTrace_2433162
  have hstable : (prefixWord ++ tailWord_2433162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433162).length < 2 ^ (prefixWord ++ tailWord_2433162).sum := by decide
  have hdescent : baseEnd_2433162 < baseStart_2433162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433228 : List Nat := [2, 2, 1, 6, 1, 2, 1, 2, 1, 4]
def baseStart_2433228 : Nat := 118140960795 + 2433228 * 2 ^ 59
def prefixEnd_2433228 : Nat := 4983230072969 + 3 ^ 40 * 2433228 * 2
def baseEnd_2433228 : Nat := 832943670652207478639863

theorem tailTrace_2433228 : CollatzResearch.WordTrace tailWord_2433228 prefixEnd_2433228 832943670652207478639863 := by
  unfold tailWord_2433228
  simp only [CollatzResearch.WordTrace]
  refine ⟨44373558014418996551454169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59164744019225328735272225 44373558014418996551454169)
  ·
    refine ⟨33280168510814247413590627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44373558014418996551454169 33280168510814247413590627)
    ·
      refine ⟨49920252766221371120385941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33280168510814247413590627 49920252766221371120385941)
      ·
        refine ⟨2340011848416626771268091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 49920252766221371120385941 2340011848416626771268091)
        ·
          refine ⟨3510017772624940156902137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2340011848416626771268091 3510017772624940156902137)
          ·
            refine ⟨2632513329468705117676603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3510017772624940156902137 2632513329468705117676603)
            ·
              refine ⟨3948769994203057676514905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2632513329468705117676603 3948769994203057676514905)
              ·
                refine ⟨2961577495652293257386179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3948769994203057676514905 2961577495652293257386179)
                ·
                  refine ⟨4442366243478439886079269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2961577495652293257386179 4442366243478439886079269)
                  ·
                    refine ⟨832943670652207478639863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4442366243478439886079269 832943670652207478639863)
                    ·
                      rfl

theorem cell22_2433228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 1, 4].length) (baseStart_2433228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2433228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2433228 prefixEnd_2433228 := by exact prefixLift 2433228
  have htrace : WordTrace (prefixWord ++ tailWord_2433228) baseStart_2433228 baseEnd_2433228 := by
    simpa [prefixWord, tailWord_2433228, baseEnd_2433228] using wordTrace_append hprefix tailTrace_2433228
  have hstable : (prefixWord ++ tailWord_2433228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433228).length < 2 ^ (prefixWord ++ tailWord_2433228).sum := by decide
  have hdescent : baseEnd_2433228 < baseStart_2433228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433303 : List Nat := [1, 1, 3, 4, 1, 3, 2, 3, 1, 3]
def baseStart_2433303 : Nat := 118140960795 + 2433303 * 2 ^ 59
def prefixEnd_2433303 : Nat := 4983230072969 + 3 ^ 40 * 2433303 * 2
def baseEnd_2433303 : Nat := 832969344684932283014633

theorem tailTrace_2433303 : CollatzResearch.WordTrace tailWord_2433303 prefixEnd_2433303 832969344684932283014633 := by
  unfold tailWord_2433303
  simp only [CollatzResearch.WordTrace]
  refine ⟨88749851503566280911888563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59166567669044187274592375 88749851503566280911888563)
  ·
    refine ⟨133124777255349421367832845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88749851503566280911888563 133124777255349421367832845)
    ·
      refine ⟨49921791470756033012937317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133124777255349421367832845 49921791470756033012937317)
      ·
        refine ⟨9360335900766756189925747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49921791470756033012937317 9360335900766756189925747)
        ·
          refine ⟨14040503851150134284888621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9360335900766756189925747 14040503851150134284888621)
          ·
            refine ⟨5265188944181300356833233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14040503851150134284888621 5265188944181300356833233)
            ·
              refine ⟨3948891708135975267624925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5265188944181300356833233 3948891708135975267624925)
              ·
                refine ⟨1480834390550990725359347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3948891708135975267624925 1480834390550990725359347)
                ·
                  refine ⟨2221251585826486088039021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1480834390550990725359347 2221251585826486088039021)
                  ·
                    refine ⟨832969344684932283014633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2221251585826486088039021 832969344684932283014633)
                    ·
                      rfl

theorem cell22_2433303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 3, 1, 3].length) (baseStart_2433303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2433303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2433303 prefixEnd_2433303 := by exact prefixLift 2433303
  have htrace : WordTrace (prefixWord ++ tailWord_2433303) baseStart_2433303 baseEnd_2433303 := by
    simpa [prefixWord, tailWord_2433303, baseEnd_2433303] using wordTrace_append hprefix tailTrace_2433303
  have hstable : (prefixWord ++ tailWord_2433303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433303).length < 2 ^ (prefixWord ++ tailWord_2433303).sum := by decide
  have hdescent : baseEnd_2433303 < baseStart_2433303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433314 : List Nat := [3, 3, 1, 1, 3, 1, 1, 2, 2, 5]
def baseStart_2433314 : Nat := 118140960795 + 2433314 * 2 ^ 59
def prefixEnd_2433314 : Nat := 4983230072969 + 3 ^ 40 * 2433314 * 2
def baseEnd_2433314 : Nat := 832973110209731920989599

theorem tailTrace_2433314 : CollatzResearch.WordTrace tailWord_2433314 prefixEnd_2433314 832973110209731920989599 := by
  unfold tailWord_2433314
  simp only [CollatzResearch.WordTrace]
  refine ⟨22187563176631607447634749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59166835137684286527025997 22187563176631607447634749)
  ·
    refine ⟨8320336191236852792863031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22187563176631607447634749 8320336191236852792863031)
    ·
      refine ⟨12480504286855279189294547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8320336191236852792863031 12480504286855279189294547)
      ·
        refine ⟨18720756430282918783941821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12480504286855279189294547 18720756430282918783941821)
        ·
          refine ⟨7020283661356094543978183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18720756430282918783941821 7020283661356094543978183)
          ·
            refine ⟨10530425492034141815967275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7020283661356094543978183 10530425492034141815967275)
            ·
              refine ⟨15795638238051212723950913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10530425492034141815967275 15795638238051212723950913)
              ·
                refine ⟨11846728678538409542963185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15795638238051212723950913 11846728678538409542963185)
                ·
                  refine ⟨8885046508903807157222389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11846728678538409542963185 8885046508903807157222389)
                  ·
                    refine ⟨832973110209731920989599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8885046508903807157222389 832973110209731920989599)
                    ·
                      rfl

theorem cell22_2433314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_2433314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2433314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2433314 prefixEnd_2433314 := by exact prefixLift 2433314
  have htrace : WordTrace (prefixWord ++ tailWord_2433314) baseStart_2433314 baseEnd_2433314 := by
    simpa [prefixWord, tailWord_2433314, baseEnd_2433314] using wordTrace_append hprefix tailTrace_2433314
  have hstable : (prefixWord ++ tailWord_2433314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433314).length < 2 ^ (prefixWord ++ tailWord_2433314).sum := by decide
  have hdescent : baseEnd_2433314 < baseStart_2433314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433316 : List Nat := [2, 3, 1, 3, 1, 4, 1, 2, 5]
def baseStart_2433316 : Nat := 118140960795 + 2433316 * 2 ^ 59
def prefixEnd_2433316 : Nat := 4983230072969 + 3 ^ 40 * 2433316 * 2
def baseEnd_2433316 : Nat := 277657931616868194146531

theorem tailTrace_2433316 : CollatzResearch.WordTrace tailWord_2433316 prefixEnd_2433316 277657931616868194146531 := by
  unfold tailWord_2433316
  simp only [CollatzResearch.WordTrace]
  refine ⟨44375162826259592066055901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59166883768346122754741201 44375162826259592066055901)
  ·
    refine ⟨16640686059847347024770963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44375162826259592066055901 16640686059847347024770963)
    ·
      refine ⟨24961029089771020537156445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16640686059847347024770963 24961029089771020537156445)
      ·
        refine ⟨9360385908664132701433667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24961029089771020537156445 9360385908664132701433667)
        ·
          refine ⟨14040578862996199052150501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9360385908664132701433667 14040578862996199052150501)
          ·
            refine ⟨2632608536811787322278219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14040578862996199052150501 2632608536811787322278219)
            ·
              refine ⟨3948912805217680983417329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2632608536811787322278219 3948912805217680983417329)
              ·
                refine ⟨2961684603913260737562997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3948912805217680983417329 2961684603913260737562997)
                ·
                  refine ⟨277657931616868194146531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2961684603913260737562997 277657931616868194146531)
                  ·
                    rfl

theorem cell22_2433316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_2433316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2433316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2433316 prefixEnd_2433316 := by exact prefixLift 2433316
  have htrace : WordTrace (prefixWord ++ tailWord_2433316) baseStart_2433316 baseEnd_2433316 := by
    simpa [prefixWord, tailWord_2433316, baseEnd_2433316] using wordTrace_append hprefix tailTrace_2433316
  have hstable : (prefixWord ++ tailWord_2433316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433316).length < 2 ^ (prefixWord ++ tailWord_2433316).sum := by decide
  have hdescent : baseEnd_2433316 < baseStart_2433316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433327 : List Nat := [1, 1, 2, 1, 2, 1, 5, 3, 6]
def baseStart_2433327 : Nat := 118140960795 + 2433327 * 2 ^ 59
def prefixEnd_2433327 : Nat := 4983230072969 + 3 ^ 40 * 2433327 * 2
def baseEnd_2433327 : Nat := 277659186791801406804853

theorem tailTrace_2433327 : CollatzResearch.WordTrace tailWord_2433327 prefixEnd_2433327 277659186791801406804853 := by
  unfold tailWord_2433327
  simp only [CollatzResearch.WordTrace]
  refine ⟨88750726855479333010762235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59167151236986222007174823 88750726855479333010762235)
  ·
    refine ⟨133126090283218999516143353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88750726855479333010762235 133126090283218999516143353)
    ·
      refine ⟨99844567712414249637107515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133126090283218999516143353 99844567712414249637107515)
      ·
        refine ⟨149766851568621374455661273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99844567712414249637107515 149766851568621374455661273)
        ·
          refine ⟨112325138676466030841745955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149766851568621374455661273 112325138676466030841745955)
          ·
            refine ⟨168487708014699046262618933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112325138676466030841745955 168487708014699046262618933)
            ·
              refine ⟨15795722626378035587120525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 168487708014699046262618933 15795722626378035587120525)
              ·
                refine ⟨5923395984891763345170197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15795722626378035587120525 5923395984891763345170197)
                ·
                  refine ⟨277659186791801406804853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5923395984891763345170197 277659186791801406804853)
                  ·
                    rfl

theorem cell22_2433327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 6].length) (baseStart_2433327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2433327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2433327 prefixEnd_2433327 := by exact prefixLift 2433327
  have htrace : WordTrace (prefixWord ++ tailWord_2433327) baseStart_2433327 baseEnd_2433327 := by
    simpa [prefixWord, tailWord_2433327, baseEnd_2433327] using wordTrace_append hprefix tailTrace_2433327
  have hstable : (prefixWord ++ tailWord_2433327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433327).length < 2 ^ (prefixWord ++ tailWord_2433327).sum := by decide
  have hdescent : baseEnd_2433327 < baseStart_2433327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433361 : List Nat := [1, 2, 2, 1, 4, 2, 3, 3, 4]
def baseStart_2433361 : Nat := 118140960795 + 2433361 * 2 ^ 59
def prefixEnd_2433361 : Nat := 4983230072969 + 3 ^ 40 * 2433361 * 2
def baseEnd_2433361 : Nat := 277663066423413155021485

theorem tailTrace_2433361 : CollatzResearch.WordTrace tailWord_2433361 prefixEnd_2433361 277663066423413155021485 := by
  unfold tailWord_2433361
  simp only [CollatzResearch.WordTrace]
  refine ⟨88751966937356156817499937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59167977958237437878333291 88751966937356156817499937)
  ·
    refine ⟨66563975203017117613124953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88751966937356156817499937 66563975203017117613124953)
    ·
      refine ⟨49922981402262838209843715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66563975203017117613124953 49922981402262838209843715)
      ·
        refine ⟨74884472103394257314765573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49922981402262838209843715 74884472103394257314765573)
        ·
          refine ⟨14040838519386423246518545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74884472103394257314765573 14040838519386423246518545)
          ·
            refine ⟨10530628889539817434888909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14040838519386423246518545 10530628889539817434888909)
            ·
              refine ⟨3948985833577431538083341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10530628889539817434888909 3948985833577431538083341)
              ·
                refine ⟨1480869687591536826781253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3948985833577431538083341 1480869687591536826781253)
                ·
                  refine ⟨277663066423413155021485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1480869687591536826781253 277663066423413155021485)
                  ·
                    rfl

theorem cell22_2433361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 3, 4].length) (baseStart_2433361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2433361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2433361 prefixEnd_2433361 := by exact prefixLift 2433361
  have htrace : WordTrace (prefixWord ++ tailWord_2433361) baseStart_2433361 baseEnd_2433361 := by
    simpa [prefixWord, tailWord_2433361, baseEnd_2433361] using wordTrace_append hprefix tailTrace_2433361
  have hstable : (prefixWord ++ tailWord_2433361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433361).length < 2 ^ (prefixWord ++ tailWord_2433361).sum := by decide
  have hdescent : baseEnd_2433361 < baseStart_2433361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433389 : List Nat := [1, 5, 1, 1, 1, 2, 4, 7]
def baseStart_2433389 : Nat := 118140960795 + 2433389 * 2 ^ 59
def prefixEnd_2433389 : Nat := 4983230072969 + 3 ^ 40 * 2433389 * 2
def baseEnd_2433389 : Nat := 92555420471384080596041

theorem tailTrace_2433389 : CollatzResearch.WordTrace tailWord_2433389 prefixEnd_2433389 92555420471384080596041 := by
  unfold tailWord_2433389
  simp only [CollatzResearch.WordTrace]
  refine ⟨88752988181254717599519221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59168658787503145066346147 88752988181254717599519221)
  ·
    refine ⟨8320592641992629774954927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88752988181254717599519221 8320592641992629774954927)
    ·
      refine ⟨12480888962988944662432391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8320592641992629774954927 12480888962988944662432391)
      ·
        refine ⟨18721333444483416993648587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12480888962988944662432391 18721333444483416993648587)
        ·
          refine ⟨28082000166725125490472881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18721333444483416993648587 28082000166725125490472881)
          ·
            refine ⟨21061500125043844117854661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28082000166725125490472881 21061500125043844117854661)
            ·
              refine ⟨3949031273445720772097749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21061500125043844117854661 3949031273445720772097749)
              ·
                refine ⟨92555420471384080596041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3949031273445720772097749 92555420471384080596041)
                ·
                  rfl

theorem cell22_2433389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 7].length) (baseStart_2433389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2433389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2433389 prefixEnd_2433389 := by exact prefixLift 2433389
  have htrace : WordTrace (prefixWord ++ tailWord_2433389) baseStart_2433389 baseEnd_2433389 := by
    simpa [prefixWord, tailWord_2433389, baseEnd_2433389] using wordTrace_append hprefix tailTrace_2433389
  have hstable : (prefixWord ++ tailWord_2433389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433389).length < 2 ^ (prefixWord ++ tailWord_2433389).sum := by decide
  have hdescent : baseEnd_2433389 < baseStart_2433389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433526 : List Nat := [5, 1, 1, 1, 2, 1, 1, 3, 1, 6]
def baseStart_2433526 : Nat := 118140960795 + 2433526 * 2 ^ 59
def prefixEnd_2433526 : Nat := 4983230072969 + 3 ^ 40 * 2433526 * 2
def baseEnd_2433526 : Nat := 833045682142234034688949

theorem tailTrace_2433526 : CollatzResearch.WordTrace tailWord_2433526 prefixEnd_2433526 833045682142234034688949 := by
  unfold tailWord_2433526
  simp only [CollatzResearch.WordTrace]
  refine ⟨5547374061359899374828527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59171989987838926664837621 5547374061359899374828527)
  ·
    refine ⟨8321061092039849062242791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5547374061359899374828527 8321061092039849062242791)
    ·
      refine ⟨12481591638059773593364187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8321061092039849062242791 12481591638059773593364187)
      ·
        refine ⟨18722387457089660390046281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12481591638059773593364187 18722387457089660390046281)
        ·
          refine ⟨14041790592817245292534711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18722387457089660390046281 14041790592817245292534711)
          ·
            refine ⟨21062685889225867938802067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14041790592817245292534711 21062685889225867938802067)
            ·
              refine ⟨31594028833838801908203101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21062685889225867938802067 31594028833838801908203101)
              ·
                refine ⟨11847760812689550715576163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31594028833838801908203101 11847760812689550715576163)
                ·
                  refine ⟨17771641219034326073364245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11847760812689550715576163 17771641219034326073364245)
                  ·
                    refine ⟨833045682142234034688949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17771641219034326073364245 833045682142234034688949)
                    ·
                      rfl

theorem cell22_2433526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_2433526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2433526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2433526 prefixEnd_2433526 := by exact prefixLift 2433526
  have htrace : WordTrace (prefixWord ++ tailWord_2433526) baseStart_2433526 baseEnd_2433526 := by
    simpa [prefixWord, tailWord_2433526, baseEnd_2433526] using wordTrace_append hprefix tailTrace_2433526
  have hstable : (prefixWord ++ tailWord_2433526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433526).length < 2 ^ (prefixWord ++ tailWord_2433526).sum := by decide
  have hdescent : baseEnd_2433526 < baseStart_2433526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433543 : List Nat := [1, 1, 4, 3, 3, 1, 1, 2, 2, 4]
def baseStart_2433543 : Nat := 118140960795 + 2433543 * 2 ^ 59
def prefixEnd_2433543 : Nat := 4983230072969 + 3 ^ 40 * 2433543 * 2
def baseEnd_2433543 : Nat := 833051501589651657013897

theorem tailTrace_2433543 : CollatzResearch.WordTrace tailWord_2433543 prefixEnd_2433543 833051501589651657013897 := by
  unfold tailWord_2433543
  simp only [CollatzResearch.WordTrace]
  refine ⟨88758605022696801900625283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59172403348464534600416855 88758605022696801900625283)
  ·
    refine ⟨133137907534045202850937925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88758605022696801900625283 133137907534045202850937925)
    ·
      refine ⟨24963357662633475534550861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133137907534045202850937925 24963357662633475534550861)
      ·
        refine ⟨9361259123487553325456573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24963357662633475534550861 9361259123487553325456573)
        ·
          refine ⟨3510472171307832497046215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9361259123487553325456573 3510472171307832497046215)
          ·
            refine ⟨5265708256961748745569323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3510472171307832497046215 5265708256961748745569323)
            ·
              refine ⟨7898562385442623118353985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5265708256961748745569323 7898562385442623118353985)
              ·
                refine ⟨5923921789081967338765489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7898562385442623118353985 5923921789081967338765489)
                ·
                  refine ⟨4442941341811475504074117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5923921789081967338765489 4442941341811475504074117)
                  ·
                    refine ⟨833051501589651657013897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4442941341811475504074117 833051501589651657013897)
                    ·
                      rfl

theorem cell22_2433543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_2433543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2433543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2433543 prefixEnd_2433543 := by exact prefixLift 2433543
  have htrace : WordTrace (prefixWord ++ tailWord_2433543) baseStart_2433543 baseEnd_2433543 := by
    simpa [prefixWord, tailWord_2433543, baseEnd_2433543] using wordTrace_append hprefix tailTrace_2433543
  have hstable : (prefixWord ++ tailWord_2433543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433543).length < 2 ^ (prefixWord ++ tailWord_2433543).sum := by decide
  have hdescent : baseEnd_2433543 < baseStart_2433543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433607 : List Nat := [1, 1, 4, 1, 4, 1, 4, 2, 1, 3]
def baseStart_2433607 : Nat := 118140960795 + 2433607 * 2 ^ 59
def prefixEnd_2433607 : Nat := 4983230072969 + 3 ^ 40 * 2433607 * 2
def baseEnd_2433607 : Nat := 833073410097576823413701

theorem tailTrace_2433607 : CollatzResearch.WordTrace tailWord_2433607 prefixEnd_2433607 833073410097576823413701 := by
  unfold tailWord_2433607
  simp only [CollatzResearch.WordTrace]
  refine ⟨88760939294464940830955075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59173959529643293887303383 88760939294464940830955075)
  ·
    refine ⟨133141408941697411246432613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88760939294464940830955075 133141408941697411246432613)
    ·
      refine ⟨24964014176568264608706115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133141408941697411246432613 24964014176568264608706115)
      ·
        refine ⟨37446021264852396913059173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24964014176568264608706115 37446021264852396913059173)
        ·
          refine ⟨7021128987159824421198595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37446021264852396913059173 7021128987159824421198595)
          ·
            refine ⟨10531693480739736631797893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7021128987159824421198595 10531693480739736631797893)
            ·
              refine ⟨1974692527638700618462105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10531693480739736631797893 1974692527638700618462105)
              ·
                refine ⟨1481019395729025463846579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1974692527638700618462105 1481019395729025463846579)
                ·
                  refine ⟨2221529093593538195769869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1481019395729025463846579 2221529093593538195769869)
                  ·
                    refine ⟨833073410097576823413701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2221529093593538195769869 833073410097576823413701)
                    ·
                      rfl

theorem cell22_2433607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_2433607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2433607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2433607 prefixEnd_2433607 := by exact prefixLift 2433607
  have htrace : WordTrace (prefixWord ++ tailWord_2433607) baseStart_2433607 baseEnd_2433607 := by
    simpa [prefixWord, tailWord_2433607, baseEnd_2433607] using wordTrace_append hprefix tailTrace_2433607
  have hstable : (prefixWord ++ tailWord_2433607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433607).length < 2 ^ (prefixWord ++ tailWord_2433607).sum := by decide
  have hdescent : baseEnd_2433607 < baseStart_2433607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433650 : List Nat := [3, 2, 1, 2, 4, 1, 1, 3, 1, 4]
def baseStart_2433650 : Nat := 118140960795 + 2433650 * 2 ^ 59
def prefixEnd_2433650 : Nat := 4983230072969 + 3 ^ 40 * 2433650 * 2
def baseEnd_2433650 : Nat := 833088129876339044588569

theorem tailTrace_2433650 : CollatzResearch.WordTrace tailWord_2433650 prefixEnd_2433650 833088129876339044588569 := by
  unfold tailWord_2433650
  simp only [CollatzResearch.WordTrace]
  refine ⟨22190626908327289793692601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59175005088872772783180269 22190626908327289793692601)
  ·
    refine ⟨16642970181245467345269451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22190626908327289793692601 16642970181245467345269451)
    ·
      refine ⟨24964455271868201017904177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16642970181245467345269451 24964455271868201017904177)
      ·
        refine ⟨18723341453901150763428133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24964455271868201017904177 18723341453901150763428133)
        ·
          refine ⟨3510626522606465768142775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18723341453901150763428133 3510626522606465768142775)
          ·
            refine ⟨5265939783909698652214163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3510626522606465768142775 5265939783909698652214163)
            ·
              refine ⟨7898909675864547978321245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5265939783909698652214163 7898909675864547978321245)
              ·
                refine ⟨2962091128449205491870467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7898909675864547978321245 2962091128449205491870467)
                ·
                  refine ⟨4443136692673808237805701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2962091128449205491870467 4443136692673808237805701)
                  ·
                    refine ⟨833088129876339044588569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4443136692673808237805701 833088129876339044588569)
                    ·
                      rfl

theorem cell22_2433650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_2433650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2433650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2433650 prefixEnd_2433650 := by exact prefixLift 2433650
  have htrace : WordTrace (prefixWord ++ tailWord_2433650) baseStart_2433650 baseEnd_2433650 := by
    simpa [prefixWord, tailWord_2433650, baseEnd_2433650] using wordTrace_append hprefix tailTrace_2433650
  have hstable : (prefixWord ++ tailWord_2433650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433650).length < 2 ^ (prefixWord ++ tailWord_2433650).sum := by decide
  have hdescent : baseEnd_2433650 < baseStart_2433650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433663 : List Nat := [1, 1, 2, 2, 1, 1, 1, 8, 2, 3]
def baseStart_2433663 : Nat := 118140960795 + 2433663 * 2 ^ 59
def prefixEnd_2433663 : Nat := 4983230072969 + 3 ^ 40 * 2433663 * 2
def baseEnd_2433663 : Nat := 833092580042011344013529

theorem tailTrace_2433663 : CollatzResearch.WordTrace tailWord_2433663 prefixEnd_2433663 833092580042011344013529 := by
  unfold tailWord_2433663
  simp only [CollatzResearch.WordTrace]
  refine ⟨88762981782262062394993643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59175321188174708263329095 88762981782262062394993643)
  ·
    refine ⟨133144472673393093592490465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88762981782262062394993643 133144472673393093592490465)
    ·
      refine ⟨99858354505044820194367849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133144472673393093592490465 99858354505044820194367849)
      ·
        refine ⟨74893765878783615145775887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99858354505044820194367849 74893765878783615145775887)
        ·
          refine ⟨112340648818175422718663831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74893765878783615145775887 112340648818175422718663831)
          ·
            refine ⟨168510973227263134077995747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112340648818175422718663831 168510973227263134077995747)
            ·
              refine ⟨252766459840894701116993621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168510973227263134077995747 252766459840894701116993621)
              ·
                refine ⟨2962106951260484778714769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 252766459840894701116993621 2962106951260484778714769)
                ·
                  refine ⟨2221580213445363584036077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2962106951260484778714769 2221580213445363584036077)
                  ·
                    refine ⟨833092580042011344013529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2221580213445363584036077 833092580042011344013529)
                    ·
                      rfl

theorem cell22_2433663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2, 3].length) (baseStart_2433663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2433663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2433663 prefixEnd_2433663 := by exact prefixLift 2433663
  have htrace : WordTrace (prefixWord ++ tailWord_2433663) baseStart_2433663 baseEnd_2433663 := by
    simpa [prefixWord, tailWord_2433663, baseEnd_2433663] using wordTrace_append hprefix tailTrace_2433663
  have hstable : (prefixWord ++ tailWord_2433663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433663).length < 2 ^ (prefixWord ++ tailWord_2433663).sum := by decide
  have hdescent : baseEnd_2433663 < baseStart_2433663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433693 : List Nat := [1, 4, 2, 1, 1, 1, 6, 6]
def baseStart_2433693 : Nat := 118140960795 + 2433693 * 2 ^ 59
def prefixEnd_2433693 : Nat := 4983230072969 + 3 ^ 40 * 2433693 * 2
def baseEnd_2433693 : Nat := 92566983295011251751493

theorem tailTrace_2433693 : CollatzResearch.WordTrace tailWord_2433693 prefixEnd_2433693 92566983295011251751493 := by
  unfold tailWord_2433693
  simp only [CollatzResearch.WordTrace]
  refine ⟨88764075972153377518585733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59176050648102251679057155 88764075972153377518585733)
  ·
    refine ⟨16643264244778758284734825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88764075972153377518585733 16643264244778758284734825)
    ·
      refine ⟨12482448183584068713551119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16643264244778758284734825 12482448183584068713551119)
      ·
        refine ⟨18723672275376103070326679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12482448183584068713551119 18723672275376103070326679)
        ·
          refine ⟨28085508413064154605490019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18723672275376103070326679 28085508413064154605490019)
          ·
            refine ⟨42128262619596231908235029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28085508413064154605490019 42128262619596231908235029)
            ·
              refine ⟨1974762310293573370698517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42128262619596231908235029 1974762310293573370698517)
              ·
                refine ⟨92566983295011251751493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1974762310293573370698517 92566983295011251751493)
                ·
                  rfl

theorem cell22_2433693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 6].length) (baseStart_2433693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2433693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2433693 prefixEnd_2433693 := by exact prefixLift 2433693
  have htrace : WordTrace (prefixWord ++ tailWord_2433693) baseStart_2433693 baseEnd_2433693 := by
    simpa [prefixWord, tailWord_2433693, baseEnd_2433693] using wordTrace_append hprefix tailTrace_2433693
  have hstable : (prefixWord ++ tailWord_2433693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433693).length < 2 ^ (prefixWord ++ tailWord_2433693).sum := by decide
  have hdescent : baseEnd_2433693 < baseStart_2433693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433710 : List Nat := [4, 1, 4, 1, 1, 3, 8]
def baseStart_2433710 : Nat := 118140960795 + 2433710 * 2 ^ 59
def prefixEnd_2433710 : Nat := 4983230072969 + 3 ^ 40 * 2433710 * 2
def baseEnd_2433710 : Nat := 30855876633426625484755

theorem tailTrace_2433710 : CollatzResearch.WordTrace tailWord_2433710 prefixEnd_2433710 30855876633426625484755 := by
  unfold tailWord_2433710
  simp only [CollatzResearch.WordTrace]
  refine ⟨11095587001636473677744323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59176464008727859614636389 11095587001636473677744323)
  ·
    refine ⟨16643380502454710516616485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11095587001636473677744323 16643380502454710516616485)
    ·
      refine ⟨3120633844210258221865591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16643380502454710516616485 3120633844210258221865591)
      ·
        refine ⟨4680950766315387332798387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3120633844210258221865591 4680950766315387332798387)
        ·
          refine ⟨7021426149473080999197581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4680950766315387332798387 7021426149473080999197581)
          ·
            refine ⟨2633034806052405374699093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7021426149473080999197581 2633034806052405374699093)
            ·
              refine ⟨30855876633426625484755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2633034806052405374699093 30855876633426625484755)
              ·
                rfl

theorem cell22_2433710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 8].length) (baseStart_2433710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2433710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2433710 prefixEnd_2433710 := by exact prefixLift 2433710
  have htrace : WordTrace (prefixWord ++ tailWord_2433710) baseStart_2433710 baseEnd_2433710 := by
    simpa [prefixWord, tailWord_2433710, baseEnd_2433710] using wordTrace_append hprefix tailTrace_2433710
  have hstable : (prefixWord ++ tailWord_2433710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433710).length < 2 ^ (prefixWord ++ tailWord_2433710).sum := by decide
  have hdescent : baseEnd_2433710 < baseStart_2433710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433725 : List Nat := [1, 4, 1, 2, 1, 3, 3, 1, 3, 3]
def baseStart_2433725 : Nat := 118140960795 + 2433725 * 2 ^ 59
def prefixEnd_2433725 : Nat := 4983230072969 + 3 ^ 40 * 2433725 * 2
def baseEnd_2433725 : Nat := 833113803909063848963339

theorem tailTrace_2433725 : CollatzResearch.WordTrace tailWord_2433725 prefixEnd_2433725 833113803909063848963339 := by
  unfold tailWord_2433725
  simp only [CollatzResearch.WordTrace]
  refine ⟨88765243108037446983750629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59176828738691631322500419 88765243108037446983750629)
  ·
    refine ⟨16643483082757021309453243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88765243108037446983750629 16643483082757021309453243)
    ·
      refine ⟨24965224624135531964179865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16643483082757021309453243 24965224624135531964179865)
      ·
        refine ⟨18723918468101648973134899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24965224624135531964179865 18723918468101648973134899)
        ·
          refine ⟨28085877702152473459702349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18723918468101648973134899 28085877702152473459702349)
          ·
            refine ⟨10532204138307177547388381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28085877702152473459702349 10532204138307177547388381)
            ·
              refine ⟨3949576551865191580270643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10532204138307177547388381 3949576551865191580270643)
              ·
                refine ⟨5924364827797787370405965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3949576551865191580270643 5924364827797787370405965)
                ·
                  refine ⟨2221636810424170263902237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5924364827797787370405965 2221636810424170263902237)
                  ·
                    refine ⟨833113803909063848963339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2221636810424170263902237 833113803909063848963339)
                    ·
                      rfl

theorem cell22_2433725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_2433725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2433725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2433725 prefixEnd_2433725 := by exact prefixLift 2433725
  have htrace : WordTrace (prefixWord ++ tailWord_2433725) baseStart_2433725 baseEnd_2433725 := by
    simpa [prefixWord, tailWord_2433725, baseEnd_2433725] using wordTrace_append hprefix tailTrace_2433725
  have hstable : (prefixWord ++ tailWord_2433725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433725).length < 2 ^ (prefixWord ++ tailWord_2433725).sum := by decide
  have hdescent : baseEnd_2433725 < baseStart_2433725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433813 : List Nat := [1, 3, 2, 1, 2, 2, 3, 1, 1, 6]
def baseStart_2433813 : Nat := 118140960795 + 2433813 * 2 ^ 59
def prefixEnd_2433813 : Nat := 4983230072969 + 3 ^ 40 * 2433813 * 2
def baseEnd_2433813 : Nat := 833143928107460952763069

theorem tailTrace_2433813 : CollatzResearch.WordTrace tailWord_2433813 prefixEnd_2433813 833143928107460952763069 := by
  unfold tailWord_2433813
  simp only [CollatzResearch.WordTrace]
  refine ⟨88768452731718638012954093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59178968487812425341969395 88768452731718638012954093)
  ·
    refine ⟨33288169774394489254857785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88768452731718638012954093 33288169774394489254857785)
    ·
      refine ⟨24966127330795866941143339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33288169774394489254857785 24966127330795866941143339)
      ·
        refine ⟨37449190996193800411715009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24966127330795866941143339 37449190996193800411715009)
        ·
          refine ⟨28086893247145350308786257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37449190996193800411715009 28086893247145350308786257)
          ·
            refine ⟨21065169935359012731589693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28086893247145350308786257 21065169935359012731589693)
            ·
              refine ⟨7899438725759629774346135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21065169935359012731589693 7899438725759629774346135)
              ·
                refine ⟨11849158088639444661519203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7899438725759629774346135 11849158088639444661519203)
                ·
                  refine ⟨17773737132959166992278805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11849158088639444661519203 17773737132959166992278805)
                  ·
                    refine ⟨833143928107460952763069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17773737132959166992278805 833143928107460952763069)
                    ·
                      rfl

theorem cell22_2433813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_2433813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2433813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2433813 prefixEnd_2433813 := by exact prefixLift 2433813
  have htrace : WordTrace (prefixWord ++ tailWord_2433813) baseStart_2433813 baseEnd_2433813 := by
    simpa [prefixWord, tailWord_2433813, baseEnd_2433813] using wordTrace_append hprefix tailTrace_2433813
  have hstable : (prefixWord ++ tailWord_2433813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433813).length < 2 ^ (prefixWord ++ tailWord_2433813).sum := by decide
  have hdescent : baseEnd_2433813 < baseStart_2433813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433920 : List Nat := [2, 1, 1, 2, 1, 2, 2, 6, 1, 4]
def baseStart_2433920 : Nat := 118140960795 + 2433920 * 2 ^ 59
def prefixEnd_2433920 : Nat := 4983230072969 + 3 ^ 40 * 2433920 * 2
def baseEnd_2433920 : Nat := 833180556394148340337741

theorem tailTrace_2433920 : CollatzResearch.WordTrace tailWord_2433920 prefixEnd_2433920 833180556394148340337741 := by
  unfold tailWord_2433920
  simp only [CollatzResearch.WordTrace]
  refine ⟨44386177671165497643549607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59181570228220663524732809 44386177671165497643549607)
  ·
    refine ⟨66579266506748246465324411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44386177671165497643549607 66579266506748246465324411)
    ·
      refine ⟨99868899760122369697986617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66579266506748246465324411 99868899760122369697986617)
      ·
        refine ⟨74901674820091777273489963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99868899760122369697986617 74901674820091777273489963)
        ·
          refine ⟨112352512230137665910234945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74901674820091777273489963 112352512230137665910234945)
          ·
            refine ⟨84264384172603249432676209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112352512230137665910234945 84264384172603249432676209)
            ·
              refine ⟨63198288129452437074507157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84264384172603249432676209 63198288129452437074507157)
              ·
                refine ⟨2962419756068082987867523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63198288129452437074507157 2962419756068082987867523)
                ·
                  refine ⟨4443629634102124481801285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2962419756068082987867523 4443629634102124481801285)
                  ·
                    refine ⟨833180556394148340337741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4443629634102124481801285 833180556394148340337741)
                    ·
                      rfl

theorem cell22_2433920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 1, 4].length) (baseStart_2433920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2433920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2433920 prefixEnd_2433920 := by exact prefixLift 2433920
  have htrace : WordTrace (prefixWord ++ tailWord_2433920) baseStart_2433920 baseEnd_2433920 := by
    simpa [prefixWord, tailWord_2433920, baseEnd_2433920] using wordTrace_append hprefix tailTrace_2433920
  have hstable : (prefixWord ++ tailWord_2433920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433920).length < 2 ^ (prefixWord ++ tailWord_2433920).sum := by decide
  have hdescent : baseEnd_2433920 < baseStart_2433920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433988 : List Nat := [2, 3, 3, 3, 1, 2, 2, 1, 1, 4]
def baseStart_2433988 : Nat := 118140960795 + 2433988 * 2 ^ 59
def prefixEnd_2433988 : Nat := 4983230072969 + 3 ^ 40 * 2433988 * 2
def baseEnd_2433988 : Nat := 833203834183818829637533

theorem tailTrace_2433988 : CollatzResearch.WordTrace tailWord_2433988 prefixEnd_2433988 833203834183818829637533 := by
  unfold tailWord_2433988
  simp only [CollatzResearch.WordTrace]
  refine ⟨44387417753042321450287309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59183223670723095267049745 44387417753042321450287309)
  ·
    refine ⟨16645281657390870543857741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44387417753042321450287309 16645281657390870543857741)
    ·
      refine ⟨6241980621521576453946653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16645281657390870543857741 6241980621521576453946653)
      ·
        refine ⟨2340742733070591170229995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6241980621521576453946653 2340742733070591170229995)
        ·
          refine ⟨3511114099605886755344993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2340742733070591170229995 3511114099605886755344993)
          ·
            refine ⟨2633335574704415066508745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3511114099605886755344993 2633335574704415066508745)
            ·
              refine ⟨1975001681028311299881559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2633335574704415066508745 1975001681028311299881559)
              ·
                refine ⟨2962502521542466949822339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1975001681028311299881559 2962502521542466949822339)
                ·
                  refine ⟨4443753782313700424733509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2962502521542466949822339 4443753782313700424733509)
                  ·
                    refine ⟨833203834183818829637533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4443753782313700424733509 833203834183818829637533)
                    ·
                      rfl

theorem cell22_2433988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_2433988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2433988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2433988 prefixEnd_2433988 := by exact prefixLift 2433988
  have htrace : WordTrace (prefixWord ++ tailWord_2433988) baseStart_2433988 baseEnd_2433988 := by
    simpa [prefixWord, tailWord_2433988, baseEnd_2433988] using wordTrace_append hprefix tailTrace_2433988
  have hstable : (prefixWord ++ tailWord_2433988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433988).length < 2 ^ (prefixWord ++ tailWord_2433988).sum := by decide
  have hdescent : baseEnd_2433988 < baseStart_2433988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434018 : List Nat := [3, 3, 3, 1, 1, 2, 3, 1, 2, 3]
def baseStart_2434018 : Nat := 118140960795 + 2434018 * 2 ^ 59
def prefixEnd_2434018 : Nat := 4983230072969 + 3 ^ 40 * 2434018 * 2
def baseEnd_2434018 : Nat := 833214103796908751387441

theorem tailTrace_2434018 : CollatzResearch.WordTrace tailWord_2434018 prefixEnd_2434018 833214103796908751387441 := by
  unfold tailWord_2434018
  simp only [CollatzResearch.WordTrace]
  refine ⟨22193982423993989506041677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59183953130650638682777805 22193982423993989506041677)
  ·
    refine ⟨8322743408997746064765629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22193982423993989506041677 8322743408997746064765629)
    ·
      refine ⟨3121028778374154774287111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8322743408997746064765629 3121028778374154774287111)
      ·
        refine ⟨4681543167561232161430667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3121028778374154774287111 4681543167561232161430667)
        ·
          refine ⟨7022314751341848242146001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4681543167561232161430667 7022314751341848242146001)
          ·
            refine ⟨5266736063506386181609501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7022314751341848242146001 5266736063506386181609501)
            ·
              refine ⟨1975026023814894818103563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5266736063506386181609501 1975026023814894818103563)
              ·
                refine ⟨2962539035722342227155345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1975026023814894818103563 2962539035722342227155345)
                ·
                  refine ⟨2221904276791756670366509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2962539035722342227155345 2221904276791756670366509)
                  ·
                    refine ⟨833214103796908751387441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2221904276791756670366509 833214103796908751387441)
                    ·
                      rfl

theorem cell22_2434018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_2434018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434018 prefixEnd_2434018 := by exact prefixLift 2434018
  have htrace : WordTrace (prefixWord ++ tailWord_2434018) baseStart_2434018 baseEnd_2434018 := by
    simpa [prefixWord, tailWord_2434018, baseEnd_2434018] using wordTrace_append hprefix tailTrace_2434018
  have hstable : (prefixWord ++ tailWord_2434018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434018).length < 2 ^ (prefixWord ++ tailWord_2434018).sum := by decide
  have hdescent : baseEnd_2434018 < baseStart_2434018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434076 : List Nat := [2, 2, 3, 1, 4, 2, 2, 1, 5]
def baseStart_2434076 : Nat := 118140960795 + 2434076 * 2 ^ 59
def prefixEnd_2434076 : Nat := 4983230072969 + 3 ^ 40 * 2434076 * 2
def baseEnd_2434076 : Nat := 277744652794071977812421

theorem tailTrace_2434076 : CollatzResearch.WordTrace tailWord_2434076 prefixEnd_2434076 277744652794071977812421 := by
  unfold tailWord_2434076
  simp only [CollatzResearch.WordTrace]
  refine ⟨44389022564882916964889041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59185363419843889286518721 44389022564882916964889041)
  ·
    refine ⟨33291766923662187723666781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44389022564882916964889041 33291766923662187723666781)
    ·
      refine ⟨12484412596373320396375043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33291766923662187723666781 12484412596373320396375043)
      ·
        refine ⟨18726618894559980594562565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12484412596373320396375043 18726618894559980594562565)
        ·
          refine ⟨3511241042729996361480481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18726618894559980594562565 3511241042729996361480481)
          ·
            refine ⟨2633430782047497271110361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3511241042729996361480481 2633430782047497271110361)
            ·
              refine ⟨1975073086535622953332771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2633430782047497271110361 1975073086535622953332771)
              ·
                refine ⟨2962609629803434429999157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1975073086535622953332771 2962609629803434429999157)
                ·
                  refine ⟨277744652794071977812421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2962609629803434429999157 277744652794071977812421)
                  ·
                    rfl

theorem cell22_2434076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 5].length) (baseStart_2434076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434076 prefixEnd_2434076 := by exact prefixLift 2434076
  have htrace : WordTrace (prefixWord ++ tailWord_2434076) baseStart_2434076 baseEnd_2434076 := by
    simpa [prefixWord, tailWord_2434076, baseEnd_2434076] using wordTrace_append hprefix tailTrace_2434076
  have hstable : (prefixWord ++ tailWord_2434076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434076).length < 2 ^ (prefixWord ++ tailWord_2434076).sum := by decide
  have hdescent : baseEnd_2434076 < baseStart_2434076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434117 : List Nat := [1, 3, 1, 1, 1, 3, 4, 2, 2, 4]
def baseStart_2434117 : Nat := 118140960795 + 2434117 * 2 ^ 59
def prefixEnd_2434117 : Nat := 4983230072969 + 3 ^ 40 * 2434117 * 2
def baseEnd_2434117 : Nat := 833247993520105493162137

theorem tailTrace_2434117 : CollatzResearch.WordTrace tailWord_2434117 prefixEnd_2434117 833247993520105493162137 := by
  unfold tailWord_2434117
  simp only [CollatzResearch.WordTrace]
  refine ⟨88779540522617297932020605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59186360348411531954680403 88779540522617297932020605)
  ·
    refine ⟨33292327695981486724507727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88779540522617297932020605 33292327695981486724507727)
    ·
      refine ⟨49938491543972230086761591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33292327695981486724507727 49938491543972230086761591)
      ·
        refine ⟨74907737315958345130142387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49938491543972230086761591 74907737315958345130142387)
        ·
          refine ⟨112361605973937517695213581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74907737315958345130142387 112361605973937517695213581)
          ·
            refine ⟨42135602240226569135705093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112361605973937517695213581 42135602240226569135705093)
            ·
              refine ⟨7900425420042481712944705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42135602240226569135705093 7900425420042481712944705)
              ·
                refine ⟨5925319065031861284708529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7900425420042481712944705 5925319065031861284708529)
                ·
                  refine ⟨4443989298773895963531397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5925319065031861284708529 4443989298773895963531397)
                  ·
                    refine ⟨833247993520105493162137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4443989298773895963531397 833247993520105493162137)
                    ·
                      rfl

theorem cell22_2434117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_2434117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434117 prefixEnd_2434117 := by exact prefixLift 2434117
  have htrace : WordTrace (prefixWord ++ tailWord_2434117) baseStart_2434117 baseEnd_2434117 := by
    simpa [prefixWord, tailWord_2434117, baseEnd_2434117] using wordTrace_append hprefix tailTrace_2434117
  have hstable : (prefixWord ++ tailWord_2434117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434117).length < 2 ^ (prefixWord ++ tailWord_2434117).sum := by decide
  have hdescent : baseEnd_2434117 < baseStart_2434117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434119 : List Nat := [1, 1, 4, 1, 3, 2, 1, 4, 2, 3]
def baseStart_2434119 : Nat := 118140960795 + 2434119 * 2 ^ 59
def prefixEnd_2434119 : Nat := 4983230072969 + 3 ^ 40 * 2434119 * 2
def baseEnd_2434119 : Nat := 833248678160978154612131

theorem tailTrace_2434119 : CollatzResearch.WordTrace tailWord_2434119 prefixEnd_2434119 833248678160978154612131 := by
  unfold tailWord_2434119
  simp only [CollatzResearch.WordTrace]
  refine ⟨88779613468610052273593411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59186408979073368182395607 88779613468610052273593411)
  ·
    refine ⟨133169420202915078410390117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88779613468610052273593411 133169420202915078410390117)
    ·
      refine ⟨24969266288046577201948147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133169420202915078410390117 24969266288046577201948147)
      ·
        refine ⟨37453899432069865802922221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24969266288046577201948147 37453899432069865802922221)
        ·
          refine ⟨14045212287026199676095833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37453899432069865802922221 14045212287026199676095833)
          ·
            refine ⟨10533909215269649757071875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14045212287026199676095833 10533909215269649757071875)
            ·
              refine ⟨15800863822904474635607813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10533909215269649757071875 15800863822904474635607813)
              ·
                refine ⟨2962661966794588994176465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15800863822904474635607813 2962661966794588994176465)
                ·
                  refine ⟨2221996475095941745632349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2962661966794588994176465 2221996475095941745632349)
                  ·
                    refine ⟨833248678160978154612131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2221996475095941745632349 833248678160978154612131)
                    ·
                      rfl

theorem cell22_2434119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_2434119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434119 prefixEnd_2434119 := by exact prefixLift 2434119
  have htrace : WordTrace (prefixWord ++ tailWord_2434119) baseStart_2434119 baseEnd_2434119 := by
    simpa [prefixWord, tailWord_2434119, baseEnd_2434119] using wordTrace_append hprefix tailTrace_2434119
  have hstable : (prefixWord ++ tailWord_2434119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434119).length < 2 ^ (prefixWord ++ tailWord_2434119).sum := by decide
  have hdescent : baseEnd_2434119 < baseStart_2434119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434132 : List Nat := [2, 4, 1, 1, 1, 1, 5, 7]
def baseStart_2434132 : Nat := 118140960795 + 2434132 * 2 ^ 59
def prefixEnd_2434132 : Nat := 4983230072969 + 3 ^ 40 * 2434132 * 2
def baseEnd_2434132 : Nat := 92583680925183383781899

theorem tailTrace_2434132 : CollatzResearch.WordTrace tailWord_2434132 prefixEnd_2434132 92583680925183383781899 := by
  unfold tailWord_2434132
  simp only [CollatzResearch.WordTrace]
  refine ⟨44390043808781477746908325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59186725078375303662544433 44390043808781477746908325)
  ·
    refine ⟨8323133214146527077545311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44390043808781477746908325 8323133214146527077545311)
    ·
      refine ⟨12484699821219790616317967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8323133214146527077545311 12484699821219790616317967)
      ·
        refine ⟨18727049731829685924476951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12484699821219790616317967 18727049731829685924476951)
        ·
          refine ⟨28090574597744528886715427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18727049731829685924476951 28090574597744528886715427)
          ·
            refine ⟨42135861896616793330073141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28090574597744528886715427 42135861896616793330073141)
            ·
              refine ⟨3950237052807824374694357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42135861896616793330073141 3950237052807824374694357)
              ·
                refine ⟨92583680925183383781899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3950237052807824374694357 92583680925183383781899)
                ·
                  rfl

theorem cell22_2434132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 7].length) (baseStart_2434132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434132 prefixEnd_2434132 := by exact prefixLift 2434132
  have htrace : WordTrace (prefixWord ++ tailWord_2434132) baseStart_2434132 baseEnd_2434132 := by
    simpa [prefixWord, tailWord_2434132, baseEnd_2434132] using wordTrace_append hprefix tailTrace_2434132
  have hstable : (prefixWord ++ tailWord_2434132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434132).length < 2 ^ (prefixWord ++ tailWord_2434132).sum := by decide
  have hdescent : baseEnd_2434132 < baseStart_2434132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434181 : List Nat := [1, 3, 1, 1, 6, 1, 2, 1, 3, 3]
def baseStart_2434181 : Nat := 118140960795 + 2434181 * 2 ^ 59
def prefixEnd_2434181 : Nat := 4983230072969 + 3 ^ 40 * 2434181 * 2
def baseEnd_2434181 : Nat := 833269902028030659561941

theorem tailTrace_2434181 : CollatzResearch.WordTrace tailWord_2434181 prefixEnd_2434181 833269902028030659561941 := by
  unfold tailWord_2434181
  simp only [CollatzResearch.WordTrace]
  refine ⟨88781874794385436862350397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59187916529590291241566931 88781874794385436862350397)
  ·
    refine ⟨33293203047894538823381399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88781874794385436862350397 33293203047894538823381399)
    ·
      refine ⟨49939804571841808235072099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33293203047894538823381399 49939804571841808235072099)
      ·
        refine ⟨74909706857762712352608149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49939804571841808235072099 74909706857762712352608149)
        ·
          refine ⟨3511392508957627141528507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 74909706857762712352608149 3511392508957627141528507)
          ·
            refine ⟨5267088763436440712292761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3511392508957627141528507 5267088763436440712292761)
            ·
              refine ⟨3950316572577330534219571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5267088763436440712292761 3950316572577330534219571)
              ·
                refine ⟨5925474858865995801329357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3950316572577330534219571 5925474858865995801329357)
                ·
                  refine ⟨2222053072074748425498509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5925474858865995801329357 2222053072074748425498509)
                  ·
                    refine ⟨833269902028030659561941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2222053072074748425498509 833269902028030659561941)
                    ·
                      rfl

theorem cell22_2434181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 3, 3].length) (baseStart_2434181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434181 prefixEnd_2434181 := by exact prefixLift 2434181
  have htrace : WordTrace (prefixWord ++ tailWord_2434181) baseStart_2434181 baseEnd_2434181 := by
    simpa [prefixWord, tailWord_2434181, baseEnd_2434181] using wordTrace_append hprefix tailTrace_2434181
  have hstable : (prefixWord ++ tailWord_2434181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434181).length < 2 ^ (prefixWord ++ tailWord_2434181).sum := by decide
  have hdescent : baseEnd_2434181 < baseStart_2434181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434215 : List Nat := [1, 1, 6, 2, 1, 3, 1, 3, 1, 3]
def baseStart_2434215 : Nat := 118140960795 + 2434215 * 2 ^ 59
def prefixEnd_2434215 : Nat := 4983230072969 + 3 ^ 40 * 2434215 * 2
def baseEnd_2434215 : Nat := 833281540922865904211837

theorem tailTrace_2434215 : CollatzResearch.WordTrace tailWord_2434215 prefixEnd_2434215 833281540922865904211837 := by
  unfold tailWord_2434215
  simp only [CollatzResearch.WordTrace]
  refine ⟨88783114876262260669088099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59188743250841507112725399 88783114876262260669088099)
  ·
    refine ⟨133174672314393391003632149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88783114876262260669088099 133174672314393391003632149)
    ·
      refine ⟨6242562764737190203295257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 133174672314393391003632149 6242562764737190203295257)
      ·
        refine ⟨4681922073552892652471443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6242562764737190203295257 4681922073552892652471443)
        ·
          refine ⟨7022883110329338978707165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4681922073552892652471443 7022883110329338978707165)
          ·
            refine ⟨2633581166373502117015187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7022883110329338978707165 2633581166373502117015187)
            ·
              refine ⟨3950371749560253175522781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2633581166373502117015187 3950371749560253175522781)
              ·
                refine ⟨1481389406085094940821043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3950371749560253175522781 1481389406085094940821043)
                ·
                  refine ⟨2222084109127642411231565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1481389406085094940821043 2222084109127642411231565)
                  ·
                    refine ⟨833281540922865904211837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2222084109127642411231565 833281540922865904211837)
                    ·
                      rfl

theorem cell22_2434215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_2434215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434215 prefixEnd_2434215 := by exact prefixLift 2434215
  have htrace : WordTrace (prefixWord ++ tailWord_2434215) baseStart_2434215 baseEnd_2434215 := by
    simpa [prefixWord, tailWord_2434215, baseEnd_2434215] using wordTrace_append hprefix tailTrace_2434215
  have hstable : (prefixWord ++ tailWord_2434215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434215).length < 2 ^ (prefixWord ++ tailWord_2434215).sum := by decide
  have hdescent : baseEnd_2434215 < baseStart_2434215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434239 : List Nat := [1, 1, 2, 2, 2, 2, 2, 6, 4]
def baseStart_2434239 : Nat := 118140960795 + 2434239 * 2 ^ 59
def prefixEnd_2434239 : Nat := 4983230072969 + 3 ^ 40 * 2434239 * 2
def baseEnd_2434239 : Nat := 277763252204445947203921

theorem tailTrace_2434239 : CollatzResearch.WordTrace tailWord_2434239 prefixEnd_2434239 277763252204445947203921 := by
  unfold tailWord_2434239
  simp only [CollatzResearch.WordTrace]
  refine ⟨88783990228175312767961771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59189326818783541845307847 88783990228175312767961771)
  ·
    refine ⟨133175985342262969151942657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88783990228175312767961771 133175985342262969151942657)
    ·
      refine ⟨99881989006697226863956993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133175985342262969151942657 99881989006697226863956993)
      ·
        refine ⟨74911491755022920147967745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99881989006697226863956993 74911491755022920147967745)
        ·
          refine ⟨56183618816267190110975809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74911491755022920147967745 56183618816267190110975809)
          ·
            refine ⟨42137714112200392583231857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56183618816267190110975809 42137714112200392583231857)
            ·
              refine ⟨31603285584150294437423893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42137714112200392583231857 31603285584150294437423893)
              ·
                refine ⟨1481404011757045051754245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31603285584150294437423893 1481404011757045051754245)
                ·
                  refine ⟨277763252204445947203921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1481404011757045051754245 277763252204445947203921)
                  ·
                    rfl

theorem cell22_2434239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6, 4].length) (baseStart_2434239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434239 prefixEnd_2434239 := by exact prefixLift 2434239
  have htrace : WordTrace (prefixWord ++ tailWord_2434239) baseStart_2434239 baseEnd_2434239 := by
    simpa [prefixWord, tailWord_2434239, baseEnd_2434239] using wordTrace_append hprefix tailTrace_2434239
  have hstable : (prefixWord ++ tailWord_2434239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434239).length < 2 ^ (prefixWord ++ tailWord_2434239).sum := by decide
  have hdescent : baseEnd_2434239 < baseStart_2434239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
