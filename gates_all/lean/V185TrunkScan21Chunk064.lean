import V185TrunkScan21Chunk063

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_773980 : List Nat := [2, 2, 4, 2, 3, 8]
def baseStart_773980 : Nat := 118140960795 + 773980 * 2 ^ 59
def prefixEnd_773980 : Nat := 4983230072969 + 3 ^ 40 * 773980 * 2
def baseEnd_773980 : Nat := 6541954847193202195729

theorem tailTrace_773980 : CollatzResearch.WordTrace tailWord_773980 prefixEnd_773980 6541954847193202195729 := by
  unfold tailWord_773980
  simp only [CollatzResearch.WordTrace]
  refine ⟨14114684868005060052651697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18819579824006746736868929 14114684868005060052651697)
  ·
    refine ⟨10586013651003795039488773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14114684868005060052651697 10586013651003795039488773)
    ·
      refine ⟨1984877559563211569904145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10586013651003795039488773 1984877559563211569904145)
      ·
        refine ⟨1488658169672408677428109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1984877559563211569904145 1488658169672408677428109)
        ·
          refine ⟨558246813627153254035541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1488658169672408677428109 558246813627153254035541)
          ·
            refine ⟨6541954847193202195729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 558246813627153254035541 6541954847193202195729)
            ·
              rfl

theorem cell21_773980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 8].length) (baseStart_773980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_773980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_773980 prefixEnd_773980 := by exact prefixLift 773980
  have htrace : WordTrace (prefixWord ++ tailWord_773980) baseStart_773980 baseEnd_773980 := by
    simpa [prefixWord, tailWord_773980, baseEnd_773980] using wordTrace_append hprefix tailTrace_773980
  have hstable : (prefixWord ++ tailWord_773980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773980).length < 2 ^ (prefixWord ++ tailWord_773980).sum := by decide
  have hdescent : baseEnd_773980 < baseStart_773980 := by decide
  rcases family_descends (prefixWord ++ tailWord_773980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774042 : List Nat := [3, 1, 1, 4, 2, 3, 1, 2, 4]
def baseStart_774042 : Nat := 118140960795 + 774042 * 2 ^ 59
def prefixEnd_774042 : Nat := 4983230072969 + 3 ^ 40 * 774042 * 2
def baseEnd_774042 : Nat := 176646930118918129251223

theorem tailTrace_774042 : CollatzResearch.WordTrace tailWord_774042 prefixEnd_774042 176646930118918129251223 := by
  unfold tailWord_774042
  simp only [CollatzResearch.WordTrace]
  refine ⟨7057907765446376173515095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18821087374523669796040253 7057907765446376173515095)
  ·
    refine ⟨10586861648169564260272643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7057907765446376173515095 10586861648169564260272643)
    ·
      refine ⟨15880292472254346390408965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10586861648169564260272643 15880292472254346390408965)
      ·
        refine ⟨2977554838547689948201681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15880292472254346390408965 2977554838547689948201681)
        ·
          refine ⟨2233166128910767461151261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2977554838547689948201681 2233166128910767461151261)
          ·
            refine ⟨837437298341537797931723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2233166128910767461151261 837437298341537797931723)
            ·
              refine ⟨1256155947512306696897585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 837437298341537797931723 1256155947512306696897585)
              ·
                refine ⟨942116960634230022673189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1256155947512306696897585 942116960634230022673189)
                ·
                  refine ⟨176646930118918129251223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 942116960634230022673189 176646930118918129251223)
                  ·
                    rfl

theorem cell21_774042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_774042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_774042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_774042 prefixEnd_774042 := by exact prefixLift 774042
  have htrace : WordTrace (prefixWord ++ tailWord_774042) baseStart_774042 baseEnd_774042 := by
    simpa [prefixWord, tailWord_774042, baseEnd_774042] using wordTrace_append hprefix tailTrace_774042
  have hstable : (prefixWord ++ tailWord_774042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774042).length < 2 ^ (prefixWord ++ tailWord_774042).sum := by decide
  have hdescent : baseEnd_774042 < baseStart_774042 := by decide
  rcases family_descends (prefixWord ++ tailWord_774042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774115 : List Nat := [1, 1, 1, 6, 1, 3, 2, 6]
def baseStart_774115 : Nat := 118140960795 + 774115 * 2 ^ 59
def prefixEnd_774115 : Nat := 4983230072969 + 3 ^ 40 * 774115 * 2
def baseEnd_774115 : Nat := 58887863237828741511469

theorem tailTrace_774115 : CollatzResearch.WordTrace tailWord_774115 prefixEnd_774115 58887863237828741511469 := by
  unfold tailWord_774115
  simp only [CollatzResearch.WordTrace]
  refine ⟨28234293590521038161467799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18822862393680692107645199 28234293590521038161467799)
  ·
    refine ⟨42351440385781557242201699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28234293590521038161467799 42351440385781557242201699)
    ·
      refine ⟨63527160578672335863302549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42351440385781557242201699 63527160578672335863302549)
      ·
        refine ⟨2977835652125265743592307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 63527160578672335863302549 2977835652125265743592307)
        ·
          refine ⟨4466753478187898615388461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2977835652125265743592307 4466753478187898615388461)
          ·
            refine ⟨1675032554320461980770673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4466753478187898615388461 1675032554320461980770673)
            ·
              refine ⟨1256274415740346485578005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1675032554320461980770673 1256274415740346485578005)
              ·
                refine ⟨58887863237828741511469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1256274415740346485578005 58887863237828741511469)
                ·
                  rfl

theorem cell21_774115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 6].length) (baseStart_774115 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_774115 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_774115 prefixEnd_774115 := by exact prefixLift 774115
  have htrace : WordTrace (prefixWord ++ tailWord_774115) baseStart_774115 baseEnd_774115 := by
    simpa [prefixWord, tailWord_774115, baseEnd_774115] using wordTrace_append hprefix tailTrace_774115
  have hstable : (prefixWord ++ tailWord_774115).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774115).length < 2 ^ (prefixWord ++ tailWord_774115).sum := by decide
  have hdescent : baseEnd_774115 < baseStart_774115 := by decide
  rcases family_descends (prefixWord ++ tailWord_774115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774143 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 8]
def baseStart_774143 : Nat := 118140960795 + 774143 * 2 ^ 59
def prefixEnd_774143 : Nat := 4983230072969 + 3 ^ 40 * 774143 * 2
def baseEnd_774143 : Nat := 176669979694964398067683

theorem tailTrace_774143 : CollatzResearch.WordTrace tailWord_774143 prefixEnd_774143 176669979694964398067683 := by
  unfold tailWord_774143
  simp only [CollatzResearch.WordTrace]
  refine ⟨28235314834419598943487083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18823543222946399295658055 28235314834419598943487083)
  ·
    refine ⟨42352972251629398415230625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28235314834419598943487083 42352972251629398415230625)
    ·
      refine ⟨31764729188722048811422969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42352972251629398415230625 31764729188722048811422969)
      ·
        refine ⟨23823546891541536608567227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31764729188722048811422969 23823546891541536608567227)
        ·
          refine ⟨35735320337312304912850841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23823546891541536608567227 35735320337312304912850841)
          ·
            refine ⟨26801490252984228684638131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35735320337312304912850841 26801490252984228684638131)
            ·
              refine ⟨40202235379476343026957197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26801490252984228684638131 40202235379476343026957197)
              ·
                refine ⟨15075838267303628635108949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40202235379476343026957197 15075838267303628635108949)
                ·
                  refine ⟨176669979694964398067683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15075838267303628635108949 176669979694964398067683)
                  ·
                    rfl

theorem cell21_774143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 8].length) (baseStart_774143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_774143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_774143 prefixEnd_774143 := by exact prefixLift 774143
  have htrace : WordTrace (prefixWord ++ tailWord_774143) baseStart_774143 baseEnd_774143 := by
    simpa [prefixWord, tailWord_774143, baseEnd_774143] using wordTrace_append hprefix tailTrace_774143
  have hstable : (prefixWord ++ tailWord_774143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774143).length < 2 ^ (prefixWord ++ tailWord_774143).sum := by decide
  have hdescent : baseEnd_774143 < baseStart_774143 := by decide
  rcases family_descends (prefixWord ++ tailWord_774143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774163 : List Nat := [1, 1, 1, 2, 1, 4, 6, 2, 3]
def baseStart_774163 : Nat := 118140960795 + 774163 * 2 ^ 59
def prefixEnd_774163 : Nat := 4983230072969 + 3 ^ 40 * 774163 * 2
def baseEnd_774163 : Nat := 176674543967448807734309

theorem tailTrace_774163 : CollatzResearch.WordTrace tailWord_774163 prefixEnd_774163 176674543967448807734309 := by
  unfold tailWord_774163
  simp only [CollatzResearch.WordTrace]
  refine ⟨28236044294347142359215143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18824029529564761572810095 28236044294347142359215143)
  ·
    refine ⟨42354066441520713538822715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28236044294347142359215143 42354066441520713538822715)
    ·
      refine ⟨63531099662281070308234073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42354066441520713538822715 63531099662281070308234073)
      ·
        refine ⟨47648324746710802731175555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63531099662281070308234073 47648324746710802731175555)
        ·
          refine ⟨71472487120066204096763333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47648324746710802731175555 71472487120066204096763333)
          ·
            refine ⟨13401091335012413268143125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71472487120066204096763333 13401091335012413268143125)
            ·
              refine ⟨628176156328706871944209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13401091335012413268143125 628176156328706871944209)
              ·
                refine ⟨471132117246530153958157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 628176156328706871944209 471132117246530153958157)
                ·
                  refine ⟨176674543967448807734309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 471132117246530153958157 176674543967448807734309)
                  ·
                    rfl

theorem cell21_774163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 2, 3].length) (baseStart_774163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_774163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_774163 prefixEnd_774163 := by exact prefixLift 774163
  have htrace : WordTrace (prefixWord ++ tailWord_774163) baseStart_774163 baseEnd_774163 := by
    simpa [prefixWord, tailWord_774163, baseEnd_774163] using wordTrace_append hprefix tailTrace_774163
  have hstable : (prefixWord ++ tailWord_774163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774163).length < 2 ^ (prefixWord ++ tailWord_774163).sum := by decide
  have hdescent : baseEnd_774163 < baseStart_774163 := by decide
  rcases family_descends (prefixWord ++ tailWord_774163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774205 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 7]
def baseStart_774205 : Nat := 118140960795 + 774205 * 2 ^ 59
def prefixEnd_774205 : Nat := 4983230072969 + 3 ^ 40 * 774205 * 2
def baseEnd_774205 : Nat := 176684128939666068034223

theorem tailTrace_774205 : CollatzResearch.WordTrace tailWord_774205 prefixEnd_774205 176684128939666068034223 := by
  unfold tailWord_774205
  simp only [CollatzResearch.WordTrace]
  refine ⟨28237576160194983532244069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18825050773463322354829379 28237576160194983532244069)
  ·
    refine ⟨5294545530036559412295763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28237576160194983532244069 5294545530036559412295763)
    ·
      refine ⟨7941818295054839118443645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5294545530036559412295763 7941818295054839118443645)
      ·
        refine ⟨2978181860645564669416367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7941818295054839118443645 2978181860645564669416367)
        ·
          refine ⟨4467272790968347004124551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2978181860645564669416367 4467272790968347004124551)
          ·
            refine ⟨6700909186452520506186827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4467272790968347004124551 6700909186452520506186827)
            ·
              refine ⟨10051363779678780759280241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6700909186452520506186827 10051363779678780759280241)
              ·
                refine ⟨7538522834759085569460181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10051363779678780759280241 7538522834759085569460181)
                ·
                  refine ⟨176684128939666068034223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7538522834759085569460181 176684128939666068034223)
                  ·
                    rfl

theorem cell21_774205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_774205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_774205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_774205 prefixEnd_774205 := by exact prefixLift 774205
  have htrace : WordTrace (prefixWord ++ tailWord_774205) baseStart_774205 baseEnd_774205 := by
    simpa [prefixWord, tailWord_774205, baseEnd_774205] using wordTrace_append hprefix tailTrace_774205
  have hstable : (prefixWord ++ tailWord_774205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774205).length < 2 ^ (prefixWord ++ tailWord_774205).sum := by decide
  have hdescent : baseEnd_774205 < baseStart_774205 := by decide
  rcases family_descends (prefixWord ++ tailWord_774205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774219 : List Nat := [1, 1, 1, 1, 3, 1, 2, 5, 6]
def baseStart_774219 : Nat := 118140960795 + 774219 * 2 ^ 59
def prefixEnd_774219 : Nat := 4983230072969 + 3 ^ 40 * 774219 * 2
def baseEnd_774219 : Nat := 176687323930405154800861

theorem tailTrace_774219 : CollatzResearch.WordTrace tailWord_774219 prefixEnd_774219 176687323930405154800861 := by
  unfold tailWord_774219
  simp only [CollatzResearch.WordTrace]
  refine ⟨28238086782144263923253711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18825391188096175948835807 28238086782144263923253711)
  ·
    refine ⟨42357130173216395884880567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28238086782144263923253711 42357130173216395884880567)
    ·
      refine ⟨63535695259824593827320851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42357130173216395884880567 63535695259824593827320851)
      ·
        refine ⟨95303542889736890740981277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63535695259824593827320851 95303542889736890740981277)
        ·
          refine ⟨35738828583651334027867979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95303542889736890740981277 35738828583651334027867979)
          ·
            refine ⟨53608242875477001041801969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35738828583651334027867979 53608242875477001041801969)
            ·
              refine ⟨40206182156607750781351477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53608242875477001041801969 40206182156607750781351477)
              ·
                refine ⟨3769329577181976635751701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40206182156607750781351477 3769329577181976635751701)
                ·
                  refine ⟨176687323930405154800861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3769329577181976635751701 176687323930405154800861)
                  ·
                    rfl

theorem cell21_774219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 6].length) (baseStart_774219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_774219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_774219 prefixEnd_774219 := by exact prefixLift 774219
  have htrace : WordTrace (prefixWord ++ tailWord_774219) baseStart_774219 baseEnd_774219 := by
    simpa [prefixWord, tailWord_774219, baseEnd_774219] using wordTrace_append hprefix tailTrace_774219
  have hstable : (prefixWord ++ tailWord_774219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774219).length < 2 ^ (prefixWord ++ tailWord_774219).sum := by decide
  have hdescent : baseEnd_774219 < baseStart_774219 := by decide
  rcases family_descends (prefixWord ++ tailWord_774219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774222 : List Nat := [4, 1, 1, 1, 1, 5, 2, 1, 5]
def baseStart_774222 : Nat := 118140960795 + 774222 * 2 ^ 59
def prefixEnd_774222 : Nat := 4983230072969 + 3 ^ 40 * 774222 * 2
def baseEnd_774222 : Nat := 176688008571277816250855

theorem tailTrace_774222 : CollatzResearch.WordTrace tailWord_774222 prefixEnd_774222 176688008571277816250855 := by
  unfold tailWord_774222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3529774525141674429451615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18825464134088930290408613 3529774525141674429451615)
  ·
    refine ⟨5294661787712511644177423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3529774525141674429451615 5294661787712511644177423)
    ·
      refine ⟨7941992681568767466266135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5294661787712511644177423 7941992681568767466266135)
      ·
        refine ⟨11912989022353151199399203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7941992681568767466266135 11912989022353151199399203)
        ·
          refine ⟨17869483533529726799098805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11912989022353151199399203 17869483533529726799098805)
          ·
            refine ⟨1675264081268411887415513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17869483533529726799098805 1675264081268411887415513)
            ·
              refine ⟨1256448060951308915561635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1675264081268411887415513 1256448060951308915561635)
              ·
                refine ⟨1884672091426963373342453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1256448060951308915561635 1884672091426963373342453)
                ·
                  refine ⟨176688008571277816250855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1884672091426963373342453 176688008571277816250855)
                  ·
                    rfl

theorem cell21_774222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_774222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_774222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_774222 prefixEnd_774222 := by exact prefixLift 774222
  have htrace : WordTrace (prefixWord ++ tailWord_774222) baseStart_774222 baseEnd_774222 := by
    simpa [prefixWord, tailWord_774222, baseEnd_774222] using wordTrace_append hprefix tailTrace_774222
  have hstable : (prefixWord ++ tailWord_774222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774222).length < 2 ^ (prefixWord ++ tailWord_774222).sum := by decide
  have hdescent : baseEnd_774222 < baseStart_774222 := by decide
  rcases family_descends (prefixWord ++ tailWord_774222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774242 : List Nat := [3, 3, 2, 2, 3, 1, 2, 5]
def baseStart_774242 : Nat := 118140960795 + 774242 * 2 ^ 59
def prefixEnd_774242 : Nat := 4983230072969 + 3 ^ 40 * 774242 * 2
def baseEnd_774242 : Nat := 58897524281254075305827

theorem tailTrace_774242 : CollatzResearch.WordTrace tailWord_774242 prefixEnd_774242 58897524281254075305827 := by
  unfold tailWord_774242
  simp only [CollatzResearch.WordTrace]
  refine ⟨7059731415265234712835245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18825950440707292567560653 7059731415265234712835245)
  ·
    refine ⟨2647399280724463017313217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7059731415265234712835245 2647399280724463017313217)
    ·
      refine ⟨1985549460543347262984913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2647399280724463017313217 1985549460543347262984913)
      ·
        refine ⟨1489162095407510447238685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1985549460543347262984913 1489162095407510447238685)
        ·
          refine ⟨558435785777816417714507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1489162095407510447238685 558435785777816417714507)
          ·
            refine ⟨837653678666724626571761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558435785777816417714507 837653678666724626571761)
            ·
              refine ⟨628240259000043469928821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 837653678666724626571761 628240259000043469928821)
              ·
                refine ⟨58897524281254075305827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 628240259000043469928821 58897524281254075305827)
                ·
                  rfl

theorem cell21_774242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 5].length) (baseStart_774242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_774242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_774242 prefixEnd_774242 := by exact prefixLift 774242
  have htrace : WordTrace (prefixWord ++ tailWord_774242) baseStart_774242 baseEnd_774242 := by
    simpa [prefixWord, tailWord_774242, baseEnd_774242] using wordTrace_append hprefix tailTrace_774242
  have hstable : (prefixWord ++ tailWord_774242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774242).length < 2 ^ (prefixWord ++ tailWord_774242).sum := by decide
  have hdescent : baseEnd_774242 < baseStart_774242 := by decide
  rcases family_descends (prefixWord ++ tailWord_774242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774324 : List Nat := [2, 5, 3, 1, 2, 1, 2, 2, 3]
def baseStart_774324 : Nat := 118140960795 + 774324 * 2 ^ 59
def prefixEnd_774324 : Nat := 4983230072969 + 3 ^ 40 * 774324 * 2
def baseEnd_774324 : Nat := 176711286360948305550647

theorem tailTrace_774324 : CollatzResearch.WordTrace tailWord_774324 prefixEnd_774324 176711286360948305550647 := by
  unfold tailWord_774324
  simp only [CollatzResearch.WordTrace]
  refine ⟨14120958223381933427913013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18827944297842577903884017 14120958223381933427913013)
  ·
    refine ⟨1323839833442056258866845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14120958223381933427913013 1323839833442056258866845)
    ·
      refine ⟨496439937540771097075067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1323839833442056258866845 496439937540771097075067)
      ·
        refine ⟨744659906311156645612601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496439937540771097075067 744659906311156645612601)
        ·
          refine ⟨558494929733367484209451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 744659906311156645612601 558494929733367484209451)
          ·
            refine ⟨837742394600051226314177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558494929733367484209451 837742394600051226314177)
            ·
              refine ⟨628306795950038419735633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 837742394600051226314177 628306795950038419735633)
              ·
                refine ⟨471230096962528814801725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 628306795950038419735633 471230096962528814801725)
                ·
                  refine ⟨176711286360948305550647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 471230096962528814801725 176711286360948305550647)
                  ·
                    rfl

theorem cell21_774324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_774324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_774324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_774324 prefixEnd_774324 := by exact prefixLift 774324
  have htrace : WordTrace (prefixWord ++ tailWord_774324) baseStart_774324 baseEnd_774324 := by
    simpa [prefixWord, tailWord_774324, baseEnd_774324] using wordTrace_append hprefix tailTrace_774324
  have hstable : (prefixWord ++ tailWord_774324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774324).length < 2 ^ (prefixWord ++ tailWord_774324).sum := by decide
  have hdescent : baseEnd_774324 < baseStart_774324 := by decide
  rcases family_descends (prefixWord ++ tailWord_774324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774447 : List Nat := [1, 1, 2, 1, 2, 1, 6, 1, 6]
def baseStart_774447 : Nat := 118140960795 + 774447 * 2 ^ 59
def prefixEnd_774447 : Nat := 4983230072969 + 3 ^ 40 * 774447 * 2
def baseEnd_774447 : Nat := 176739356636727425000395

theorem tailTrace_774447 : CollatzResearch.WordTrace tailWord_774447 prefixEnd_774447 176739356636727425000395 := by
  unfold tailWord_774447
  simp only [CollatzResearch.WordTrace]
  refine ⟨28246402625318258862553595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18830935083545505908369063 28246402625318258862553595)
  ·
    refine ⟨42369603937977388293830393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28246402625318258862553595 42369603937977388293830393)
    ·
      refine ⟨31777202953483041220372795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42369603937977388293830393 31777202953483041220372795)
      ·
        refine ⟨47665804430224561830559193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31777202953483041220372795 47665804430224561830559193)
        ·
          refine ⟨35749353322668421372919395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47665804430224561830559193 35749353322668421372919395)
          ·
            refine ⟨53624029984002632059379093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35749353322668421372919395 53624029984002632059379093)
            ·
              refine ⟨2513626405500123377783395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53624029984002632059379093 2513626405500123377783395)
              ·
                refine ⟨3770439608250185066675093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2513626405500123377783395 3770439608250185066675093)
                ·
                  refine ⟨176739356636727425000395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3770439608250185066675093 176739356636727425000395)
                  ·
                    rfl

theorem cell21_774447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 6].length) (baseStart_774447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_774447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_774447 prefixEnd_774447 := by exact prefixLift 774447
  have htrace : WordTrace (prefixWord ++ tailWord_774447) baseStart_774447 baseEnd_774447 := by
    simpa [prefixWord, tailWord_774447, baseEnd_774447] using wordTrace_append hprefix tailTrace_774447
  have hstable : (prefixWord ++ tailWord_774447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774447).length < 2 ^ (prefixWord ++ tailWord_774447).sum := by decide
  have hdescent : baseEnd_774447 < baseStart_774447 := by decide
  rcases family_descends (prefixWord ++ tailWord_774447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774509 : List Nat := [1, 5, 1, 1, 1, 2, 2, 3, 5]
def baseStart_774509 : Nat := 118140960795 + 774509 * 2 ^ 59
def prefixEnd_774509 : Nat := 4983230072969 + 3 ^ 40 * 774509 * 2
def baseEnd_774509 : Nat := 176753505881429094966935

theorem tailTrace_774509 : CollatzResearch.WordTrace tailWord_774509 prefixEnd_774509 176753505881429094966935 := by
  unfold tailWord_774509
  simp only [CollatzResearch.WordTrace]
  refine ⟨28248663951093643451310581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18832442634062428967540387 28248663951093643451310581)
  ·
    refine ⟨2648312245415029073560367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28248663951093643451310581 2648312245415029073560367)
    ·
      refine ⟨3972468368122543610340551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2648312245415029073560367 3972468368122543610340551)
      ·
        refine ⟨5958702552183815415510827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3972468368122543610340551 5958702552183815415510827)
        ·
          refine ⟨8938053828275723123266241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5958702552183815415510827 8938053828275723123266241)
          ·
            refine ⟨6703540371206792342449681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8938053828275723123266241 6703540371206792342449681)
            ·
              refine ⟨5027655278405094256837261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6703540371206792342449681 5027655278405094256837261)
              ·
                refine ⟨1885370729401910346313973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5027655278405094256837261 1885370729401910346313973)
                ·
                  refine ⟨176753505881429094966935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1885370729401910346313973 176753505881429094966935)
                  ·
                    rfl

theorem cell21_774509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_774509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_774509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_774509 prefixEnd_774509 := by exact prefixLift 774509
  have htrace : WordTrace (prefixWord ++ tailWord_774509) baseStart_774509 baseEnd_774509 := by
    simpa [prefixWord, tailWord_774509, baseEnd_774509] using wordTrace_append hprefix tailTrace_774509
  have hstable : (prefixWord ++ tailWord_774509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774509).length < 2 ^ (prefixWord ++ tailWord_774509).sum := by decide
  have hdescent : baseEnd_774509 < baseStart_774509 := by decide
  rcases family_descends (prefixWord ++ tailWord_774509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774554 : List Nat := [3, 1, 1, 4, 1, 3, 8]
def baseStart_774554 : Nat := 118140960795 + 774554 * 2 ^ 59
def prefixEnd_774554 : Nat := 4983230072969 + 3 ^ 40 * 774554 * 2
def baseEnd_774554 : Nat := 19640419499391001857427

theorem tailTrace_774554 : CollatzResearch.WordTrace tailWord_774554 prefixEnd_774554 19640419499391001857427 := by
  unfold tailWord_774554
  simp only [CollatzResearch.WordTrace]
  refine ⟨7062576308982654034174679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18833536823953744091132477 7062576308982654034174679)
  ·
    refine ⟨10593864463473981051262019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7062576308982654034174679 10593864463473981051262019)
    ·
      refine ⟨15890796695210971576893029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10593864463473981051262019 15890796695210971576893029)
      ·
        refine ⟨2979524380352057170667443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15890796695210971576893029 2979524380352057170667443)
        ·
          refine ⟨4469286570528085756001165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2979524380352057170667443 4469286570528085756001165)
          ·
            refine ⟨1675982463948032158500437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4469286570528085756001165 1675982463948032158500437)
            ·
              refine ⟨19640419499391001857427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1675982463948032158500437 19640419499391001857427)
              ·
                rfl

theorem cell21_774554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 8].length) (baseStart_774554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_774554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_774554 prefixEnd_774554 := by exact prefixLift 774554
  have htrace : WordTrace (prefixWord ++ tailWord_774554) baseStart_774554 baseEnd_774554 := by
    simpa [prefixWord, tailWord_774554, baseEnd_774554] using wordTrace_append hprefix tailTrace_774554
  have hstable : (prefixWord ++ tailWord_774554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774554).length < 2 ^ (prefixWord ++ tailWord_774554).sum := by decide
  have hdescent : baseEnd_774554 < baseStart_774554 := by decide
  rcases family_descends (prefixWord ++ tailWord_774554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774585 : List Nat := [1, 2, 1, 4, 3, 1, 2, 2, 5]
def baseStart_774585 : Nat := 118140960795 + 774585 * 2 ^ 59
def prefixEnd_774585 : Nat := 4983230072969 + 3 ^ 40 * 774585 * 2
def baseEnd_774585 : Nat := 176770850116869851700113

theorem tailTrace_774585 : CollatzResearch.WordTrace tailWord_774585 prefixEnd_774585 176770850116869851700113 := by
  unfold tailWord_774585
  simp only [CollatzResearch.WordTrace]
  refine ⟨28251435898818308431077209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18834290599212205620718139 28251435898818308431077209)
  ·
    refine ⟨21188576924113731323307907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28251435898818308431077209 21188576924113731323307907)
    ·
      refine ⟨31782865386170596984961861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21188576924113731323307907 31782865386170596984961861)
      ·
        refine ⟨5959287259906986934680349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31782865386170596984961861 5959287259906986934680349)
        ·
          refine ⟨2234732722465120100505131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5959287259906986934680349 2234732722465120100505131)
          ·
            refine ⟨3352099083697680150757697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2234732722465120100505131 3352099083697680150757697)
            ·
              refine ⟨2514074312773260113068273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3352099083697680150757697 2514074312773260113068273)
              ·
                refine ⟨1885555734579945084801205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2514074312773260113068273 1885555734579945084801205)
                ·
                  refine ⟨176770850116869851700113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1885555734579945084801205 176770850116869851700113)
                  ·
                    rfl

theorem cell21_774585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 5].length) (baseStart_774585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_774585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_774585 prefixEnd_774585 := by exact prefixLift 774585
  have htrace : WordTrace (prefixWord ++ tailWord_774585) baseStart_774585 baseEnd_774585 := by
    simpa [prefixWord, tailWord_774585, baseEnd_774585] using wordTrace_append hprefix tailTrace_774585
  have hstable : (prefixWord ++ tailWord_774585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774585).length < 2 ^ (prefixWord ++ tailWord_774585).sum := by decide
  have hdescent : baseEnd_774585 < baseStart_774585 := by decide
  rcases family_descends (prefixWord ++ tailWord_774585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774588 : List Nat := [2, 2, 2, 4, 1, 3, 2, 5]
def baseStart_774588 : Nat := 118140960795 + 774588 * 2 ^ 59
def prefixEnd_774588 : Nat := 4983230072969 + 3 ^ 40 * 774588 * 2
def baseEnd_774588 : Nat := 58923844919247504383369

theorem tailTrace_774588 : CollatzResearch.WordTrace tailWord_774588 prefixEnd_774588 58923844919247504383369 := by
  unfold tailWord_774588
  simp only [CollatzResearch.WordTrace]
  refine ⟨14125772658903719971718209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18834363545204959962290945 14125772658903719971718209)
  ·
    refine ⟨10594329494177789978788657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14125772658903719971718209 10594329494177789978788657)
    ·
      refine ⟨7945747120633342484091493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10594329494177789978788657 7945747120633342484091493)
      ·
        refine ⟨1489827585118751715767155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7945747120633342484091493 1489827585118751715767155)
        ·
          refine ⟨2234741377678127573650733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1489827585118751715767155 2234741377678127573650733)
          ·
            refine ⟨838028016629297840119025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2234741377678127573650733 838028016629297840119025)
            ·
              refine ⟨628521012471973380089269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 838028016629297840119025 628521012471973380089269)
              ·
                refine ⟨58923844919247504383369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 628521012471973380089269 58923844919247504383369)
                ·
                  rfl

theorem cell21_774588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 5].length) (baseStart_774588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_774588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_774588 prefixEnd_774588 := by exact prefixLift 774588
  have htrace : WordTrace (prefixWord ++ tailWord_774588) baseStart_774588 baseEnd_774588 := by
    simpa [prefixWord, tailWord_774588, baseEnd_774588] using wordTrace_append hprefix tailTrace_774588
  have hstable : (prefixWord ++ tailWord_774588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774588).length < 2 ^ (prefixWord ++ tailWord_774588).sum := by decide
  have hdescent : baseEnd_774588 < baseStart_774588 := by decide
  rcases family_descends (prefixWord ++ tailWord_774588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774599 : List Nat := [1, 1, 4, 1, 1, 4, 1, 2, 6]
def baseStart_774599 : Nat := 118140960795 + 774599 * 2 ^ 59
def prefixEnd_774599 : Nat := 4983230072969 + 3 ^ 40 * 774599 * 2
def baseEnd_774599 : Nat := 176774045107608938466751

theorem tailTrace_774599 : CollatzResearch.WordTrace tailWord_774599 prefixEnd_774599 176774045107608938466751 := by
  unfold tailWord_774599
  simp only [CollatzResearch.WordTrace]
  refine ⟨28251946520767588822086851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18834631013845059214724567 28251946520767588822086851)
  ·
    refine ⟨42377919781151383233130277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28251946520767588822086851 42377919781151383233130277)
    ·
      refine ⟨7945859958965884356211927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42377919781151383233130277 7945859958965884356211927)
      ·
        refine ⟨11918789938448826534317891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7945859958965884356211927 11918789938448826534317891)
        ·
          refine ⟨17878184907673239801476837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11918789938448826534317891 17878184907673239801476837)
          ·
            refine ⟨3352159670188732462776907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17878184907673239801476837 3352159670188732462776907)
            ·
              refine ⟨5028239505283098694165361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3352159670188732462776907 5028239505283098694165361)
              ·
                refine ⟨3771179628962324020624021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5028239505283098694165361 3771179628962324020624021)
                ·
                  refine ⟨176774045107608938466751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3771179628962324020624021 176774045107608938466751)
                  ·
                    rfl

theorem cell21_774599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 6].length) (baseStart_774599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_774599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_774599 prefixEnd_774599 := by exact prefixLift 774599
  have htrace : WordTrace (prefixWord ++ tailWord_774599) baseStart_774599 baseEnd_774599 := by
    simpa [prefixWord, tailWord_774599, baseEnd_774599] using wordTrace_append hprefix tailTrace_774599
  have hstable : (prefixWord ++ tailWord_774599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774599).length < 2 ^ (prefixWord ++ tailWord_774599).sum := by decide
  have hdescent : baseEnd_774599 < baseStart_774599 := by decide
  rcases family_descends (prefixWord ++ tailWord_774599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774695 : List Nat := [1, 1, 7, 2, 1, 1, 1, 2, 5]
def baseStart_774695 : Nat := 118140960795 + 774695 * 2 ^ 59
def prefixEnd_774695 : Nat := 4983230072969 + 3 ^ 40 * 774695 * 2
def baseEnd_774695 : Nat := 176795953615534104866555

theorem tailTrace_774695 : CollatzResearch.WordTrace tailWord_774695 prefixEnd_774695 176795953615534104866555 := by
  unfold tailWord_774695
  simp only [CollatzResearch.WordTrace]
  refine ⟨28255447928419797217581539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18836965285613198145054359 28255447928419797217581539)
  ·
    refine ⟨42383171892629695826372309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28255447928419797217581539 42383171892629695826372309)
    ·
      refine ⟨993355591233508495930601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 42383171892629695826372309 993355591233508495930601)
      ·
        refine ⟨745016693425131371947951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 993355591233508495930601 745016693425131371947951)
        ·
          refine ⟨1117525040137697057921927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745016693425131371947951 1117525040137697057921927)
          ·
            refine ⟨1676287560206545586882891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1117525040137697057921927 1676287560206545586882891)
            ·
              refine ⟨2514431340309818380324337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1676287560206545586882891 2514431340309818380324337)
              ·
                refine ⟨1885823505232363785243253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2514431340309818380324337 1885823505232363785243253)
                ·
                  refine ⟨176795953615534104866555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1885823505232363785243253 176795953615534104866555)
                  ·
                    rfl

theorem cell21_774695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 5].length) (baseStart_774695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_774695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_774695 prefixEnd_774695 := by exact prefixLift 774695
  have htrace : WordTrace (prefixWord ++ tailWord_774695) baseStart_774695 baseEnd_774695 := by
    simpa [prefixWord, tailWord_774695, baseEnd_774695] using wordTrace_append hprefix tailTrace_774695
  have hstable : (prefixWord ++ tailWord_774695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774695).length < 2 ^ (prefixWord ++ tailWord_774695).sum := by decide
  have hdescent : baseEnd_774695 < baseStart_774695 := by decide
  rcases family_descends (prefixWord ++ tailWord_774695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774726 : List Nat := [6, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_774726 : Nat := 118140960795 + 774726 * 2 ^ 59
def prefixEnd_774726 : Nat := 4983230072969 + 3 ^ 40 * 774726 * 2
def baseEnd_774726 : Nat := 176803028237884939849825

theorem tailTrace_774726 : CollatzResearch.WordTrace tailWord_774726 prefixEnd_774726 176803028237884939849825 := by
  unfold tailWord_774726
  simp only [CollatzResearch.WordTrace]
  refine ⟨883018080978359047248751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18837719060871659674640021 883018080978359047248751)
  ·
    refine ⟨1324527121467538570873127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 883018080978359047248751 1324527121467538570873127)
    ·
      refine ⟨1986790682201307856309691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1324527121467538570873127 1986790682201307856309691)
      ·
        refine ⟨2980186023301961784464537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1986790682201307856309691 2980186023301961784464537)
        ·
          refine ⟨2235139517476471338348403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2980186023301961784464537 2235139517476471338348403)
          ·
            refine ⟨3352709276214707007522605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235139517476471338348403 3352709276214707007522605)
            ·
              refine ⟨1257265978580515127820977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3352709276214707007522605 1257265978580515127820977)
              ·
                refine ⟨942949483935386345865733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1257265978580515127820977 942949483935386345865733)
                ·
                  refine ⟨176803028237884939849825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 942949483935386345865733 176803028237884939849825)
                  ·
                    rfl

theorem cell21_774726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_774726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_774726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_774726 prefixEnd_774726 := by exact prefixLift 774726
  have htrace : WordTrace (prefixWord ++ tailWord_774726) baseStart_774726 baseEnd_774726 := by
    simpa [prefixWord, tailWord_774726, baseEnd_774726] using wordTrace_append hprefix tailTrace_774726
  have hstable : (prefixWord ++ tailWord_774726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774726).length < 2 ^ (prefixWord ++ tailWord_774726).sum := by decide
  have hdescent : baseEnd_774726 < baseStart_774726 := by decide
  rcases family_descends (prefixWord ++ tailWord_774726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774737 : List Nat := [1, 2, 2, 1, 3, 4, 2, 1, 5]
def baseStart_774737 : Nat := 118140960795 + 774737 * 2 ^ 59
def prefixEnd_774737 : Nat := 4983230072969 + 3 ^ 40 * 774737 * 2
def baseEnd_774737 : Nat := 176805538587751365166469

theorem tailTrace_774737 : CollatzResearch.WordTrace tailWord_774737 prefixEnd_774737 176805538587751365166469 := by
  unfold tailWord_774737
  simp only [CollatzResearch.WordTrace]
  refine ⟨28256979794267638390610465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18837986529511758927073643 28256979794267638390610465)
  ·
    refine ⟨21192734845700728792957849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28256979794267638390610465 21192734845700728792957849)
    ·
      refine ⟨15894551134275546594718387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21192734845700728792957849 15894551134275546594718387)
      ·
        refine ⟨23841826701413319892077581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15894551134275546594718387 23841826701413319892077581)
        ·
          refine ⟨8940685013029994959529093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23841826701413319892077581 8940685013029994959529093)
          ·
            refine ⟨1676378439943124054911705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8940685013029994959529093 1676378439943124054911705)
            ·
              refine ⟨1257283829957343041183779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1676378439943124054911705 1257283829957343041183779)
              ·
                refine ⟨1885925744936014561775669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1257283829957343041183779 1885925744936014561775669)
                ·
                  refine ⟨176805538587751365166469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1885925744936014561775669 176805538587751365166469)
                  ·
                    rfl

theorem cell21_774737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 5].length) (baseStart_774737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_774737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_774737 prefixEnd_774737 := by exact prefixLift 774737
  have htrace : WordTrace (prefixWord ++ tailWord_774737) baseStart_774737 baseEnd_774737 := by
    simpa [prefixWord, tailWord_774737, baseEnd_774737] using wordTrace_append hprefix tailTrace_774737
  have hstable : (prefixWord ++ tailWord_774737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774737).length < 2 ^ (prefixWord ++ tailWord_774737).sum := by decide
  have hdescent : baseEnd_774737 < baseStart_774737 := by decide
  rcases family_descends (prefixWord ++ tailWord_774737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774751 : List Nat := [1, 1, 2, 3, 1, 1, 1, 7, 4]
def baseStart_774751 : Nat := 118140960795 + 774751 * 2 ^ 59
def prefixEnd_774751 : Nat := 4983230072969 + 3 ^ 40 * 774751 * 2
def baseEnd_774751 : Nat := 176808733578490451933107

theorem tailTrace_774751 : CollatzResearch.WordTrace tailWord_774751 prefixEnd_774751 176808733578490451933107 := by
  unfold tailWord_774751
  simp only [CollatzResearch.WordTrace]
  refine ⟨28257490416216918781620107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18838326944144612521080071 28257490416216918781620107)
  ·
    refine ⟨42386235624325378172430161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28257490416216918781620107 42386235624325378172430161)
    ·
      refine ⟨31789676718244033629322621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42386235624325378172430161 31789676718244033629322621)
      ·
        refine ⟨11921128769341512610995983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31789676718244033629322621 11921128769341512610995983)
        ·
          refine ⟨17881693154012268916493975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11921128769341512610995983 17881693154012268916493975)
          ·
            refine ⟨26822539731018403374740963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17881693154012268916493975 26822539731018403374740963)
            ·
              refine ⟨40233809596527605062111445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26822539731018403374740963 40233809596527605062111445)
              ·
                refine ⟨942979912418615743643237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 40233809596527605062111445 942979912418615743643237)
                ·
                  refine ⟨176808733578490451933107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 942979912418615743643237 176808733578490451933107)
                  ·
                    rfl

theorem cell21_774751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 4].length) (baseStart_774751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_774751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_774751 prefixEnd_774751 := by exact prefixLift 774751
  have htrace : WordTrace (prefixWord ++ tailWord_774751) baseStart_774751 baseEnd_774751 := by
    simpa [prefixWord, tailWord_774751, baseEnd_774751] using wordTrace_append hprefix tailTrace_774751
  have hstable : (prefixWord ++ tailWord_774751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774751).length < 2 ^ (prefixWord ++ tailWord_774751).sum := by decide
  have hdescent : baseEnd_774751 < baseStart_774751 := by decide
  rcases family_descends (prefixWord ++ tailWord_774751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774796 : List Nat := [2, 2, 1, 2, 1, 1, 2, 5, 5]
def baseStart_774796 : Nat := 118140960795 + 774796 * 2 ^ 59
def prefixEnd_774796 : Nat := 4983230072969 + 3 ^ 40 * 774796 * 2
def baseEnd_774796 : Nat := 176819003191580373683015

theorem tailTrace_774796 : CollatzResearch.WordTrace tailWord_774796 prefixEnd_774796 176819003191580373683015 := by
  unfold tailWord_774796
  simp only [CollatzResearch.WordTrace]
  refine ⟨14129565850526945733504121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18839421134035927644672161 14129565850526945733504121)
  ·
    refine ⟨10597174387895209300128091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14129565850526945733504121 10597174387895209300128091)
    ·
      refine ⟨15895761581842813950192137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10597174387895209300128091 15895761581842813950192137)
      ·
        refine ⟨11921821186382110462644103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15895761581842813950192137 11921821186382110462644103)
        ·
          refine ⟨17882731779573165693966155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11921821186382110462644103 17882731779573165693966155)
          ·
            refine ⟨26824097669359748540949233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17882731779573165693966155 26824097669359748540949233)
            ·
              refine ⟨20118073252019811405711925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26824097669359748540949233 20118073252019811405711925)
              ·
                refine ⟨1886069367376857319285493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20118073252019811405711925 1886069367376857319285493)
                ·
                  refine ⟨176819003191580373683015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1886069367376857319285493 176819003191580373683015)
                  ·
                    rfl

theorem cell21_774796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_774796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_774796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_774796 prefixEnd_774796 := by exact prefixLift 774796
  have htrace : WordTrace (prefixWord ++ tailWord_774796) baseStart_774796 baseEnd_774796 := by
    simpa [prefixWord, tailWord_774796, baseEnd_774796] using wordTrace_append hprefix tailTrace_774796
  have hstable : (prefixWord ++ tailWord_774796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774796).length < 2 ^ (prefixWord ++ tailWord_774796).sum := by decide
  have hdescent : baseEnd_774796 < baseStart_774796 := by decide
  rcases family_descends (prefixWord ++ tailWord_774796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774802 : List Nat := [3, 2, 3, 1, 2, 3, 2, 1, 4]
def baseStart_774802 : Nat := 118140960795 + 774802 * 2 ^ 59
def prefixEnd_774802 : Nat := 4983230072969 + 3 ^ 40 * 774802 * 2
def baseEnd_774802 : Nat := 176820372473325696583003

theorem tailTrace_774802 : CollatzResearch.WordTrace tailWord_774802 prefixEnd_774802 176820372473325696583003 := by
  unfold tailWord_774802
  simp only [CollatzResearch.WordTrace]
  refine ⟨7064837634758038622931665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18839567026021436327817773 7064837634758038622931665)
  ·
    refine ⟨5298628226068528967198749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7064837634758038622931665 5298628226068528967198749)
    ·
      refine ⟨1986985584775698362699531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5298628226068528967198749 1986985584775698362699531)
      ·
        refine ⟨2980478377163547544049297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1986985584775698362699531 2980478377163547544049297)
        ·
          refine ⟨2235358782872660658036973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2980478377163547544049297 2235358782872660658036973)
          ·
            refine ⟨838259543577247746763865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2235358782872660658036973 838259543577247746763865)
            ·
              refine ⟨628694657682935810072899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 838259543577247746763865 628694657682935810072899)
              ·
                refine ⟨943041986524403715109349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 628694657682935810072899 943041986524403715109349)
                ·
                  refine ⟨176820372473325696583003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 943041986524403715109349 176820372473325696583003)
                  ·
                    rfl

theorem cell21_774802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_774802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_774802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_774802 prefixEnd_774802 := by exact prefixLift 774802
  have htrace : WordTrace (prefixWord ++ tailWord_774802) baseStart_774802 baseEnd_774802 := by
    simpa [prefixWord, tailWord_774802, baseEnd_774802] using wordTrace_append hprefix tailTrace_774802
  have hstable : (prefixWord ++ tailWord_774802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774802).length < 2 ^ (prefixWord ++ tailWord_774802).sum := by decide
  have hdescent : baseEnd_774802 < baseStart_774802 := by decide
  rcases family_descends (prefixWord ++ tailWord_774802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774844 : List Nat := [2, 2, 2, 3, 1, 1, 4, 2, 4]
def baseStart_774844 : Nat := 118140960795 + 774844 * 2 ^ 59
def prefixEnd_774844 : Nat := 4983230072969 + 3 ^ 40 * 774844 * 2
def baseEnd_774844 : Nat := 176829957445542956882917

theorem tailTrace_774844 : CollatzResearch.WordTrace tailWord_774844 prefixEnd_774844 176829957445542956882917 := by
  unfold tailWord_774844
  simp only [CollatzResearch.WordTrace]
  refine ⟨14130441202439997832377793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18840588269919997109837057 14130441202439997832377793)
  ·
    refine ⟨10597830901829998374283345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14130441202439997832377793 10597830901829998374283345)
    ·
      refine ⟨7948373176372498780712509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10597830901829998374283345 7948373176372498780712509)
      ·
        refine ⟨2980639941139687042767191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7948373176372498780712509 2980639941139687042767191)
        ·
          refine ⟨4470959911709530564150787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2980639941139687042767191 4470959911709530564150787)
          ·
            refine ⟨6706439867564295846226181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4470959911709530564150787 6706439867564295846226181)
            ·
              refine ⟨1257457475168305471167409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6706439867564295846226181 1257457475168305471167409)
              ·
                refine ⟨943093106376229103375557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1257457475168305471167409 943093106376229103375557)
                ·
                  refine ⟨176829957445542956882917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 943093106376229103375557 176829957445542956882917)
                  ·
                    rfl

theorem cell21_774844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_774844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_774844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_774844 prefixEnd_774844 := by exact prefixLift 774844
  have htrace : WordTrace (prefixWord ++ tailWord_774844) baseStart_774844 baseEnd_774844 := by
    simpa [prefixWord, tailWord_774844, baseEnd_774844] using wordTrace_append hprefix tailTrace_774844
  have hstable : (prefixWord ++ tailWord_774844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774844).length < 2 ^ (prefixWord ++ tailWord_774844).sum := by decide
  have hdescent : baseEnd_774844 < baseStart_774844 := by decide
  rcases family_descends (prefixWord ++ tailWord_774844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774847 : List Nat := [1, 1, 2, 2, 2, 6, 2, 2, 3]
def baseStart_774847 : Nat := 118140960795 + 774847 * 2 ^ 59
def prefixEnd_774847 : Nat := 4983230072969 + 3 ^ 40 * 774847 * 2
def baseEnd_774847 : Nat := 176830642086415618332911

theorem tailTrace_774847 : CollatzResearch.WordTrace tailWord_774847 prefixEnd_774847 176830642086415618332911 := by
  unfold tailWord_774847
  simp only [CollatzResearch.WordTrace]
  refine ⟨28260991823869127177114795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18840661215912751451409863 28260991823869127177114795)
  ·
    refine ⟨42391487735803690765672193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28260991823869127177114795 42391487735803690765672193)
    ·
      refine ⟨31793615801852768074254145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42391487735803690765672193 31793615801852768074254145)
      ·
        refine ⟨23845211851389576055690609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31793615801852768074254145 23845211851389576055690609)
        ·
          refine ⟨17883908888542182041767957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23845211851389576055690609 17883908888542182041767957)
          ·
            refine ⟨838308229150414783207873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17883908888542182041767957 838308229150414783207873)
            ·
              refine ⟨628731171862811087405905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 838308229150414783207873 628731171862811087405905)
              ·
                refine ⟨471548378897108315554429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 628731171862811087405905 471548378897108315554429)
                ·
                  refine ⟨176830642086415618332911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 471548378897108315554429 176830642086415618332911)
                  ·
                    rfl

theorem cell21_774847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 2, 3].length) (baseStart_774847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_774847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_774847 prefixEnd_774847 := by exact prefixLift 774847
  have htrace : WordTrace (prefixWord ++ tailWord_774847) baseStart_774847 baseEnd_774847 := by
    simpa [prefixWord, tailWord_774847, baseEnd_774847] using wordTrace_append hprefix tailTrace_774847
  have hstable : (prefixWord ++ tailWord_774847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774847).length < 2 ^ (prefixWord ++ tailWord_774847).sum := by decide
  have hdescent : baseEnd_774847 < baseStart_774847 := by decide
  rcases family_descends (prefixWord ++ tailWord_774847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774858 : List Nat := [3, 1, 2, 1, 4, 1, 3, 6]
def baseStart_774858 : Nat := 118140960795 + 774858 * 2 ^ 59
def prefixEnd_774858 : Nat := 4983230072969 + 3 ^ 40 * 774858 * 2
def baseEnd_774858 : Nat := 58944384145427347883185

theorem tailTrace_774858 : CollatzResearch.WordTrace tailWord_774858 prefixEnd_774858 58944384145427347883185 := by
  unfold tailWord_774858
  simp only [CollatzResearch.WordTrace]
  refine ⟨7065348256707319013941307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18840928684552850703843485 7065348256707319013941307)
  ·
    refine ⟨10598022385060978520911961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7065348256707319013941307 10598022385060978520911961)
    ·
      refine ⟨7948516788795733890683971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10598022385060978520911961 7948516788795733890683971)
      ·
        refine ⟨11922775183193600836025957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7948516788795733890683971 11922775183193600836025957)
        ·
          refine ⟨2235520346848800156754867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11922775183193600836025957 2235520346848800156754867)
          ·
            refine ⟨3353280520273200235132301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235520346848800156754867 3353280520273200235132301)
            ·
              refine ⟨1257480195102450088174613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3353280520273200235132301 1257480195102450088174613)
              ·
                refine ⟨58944384145427347883185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1257480195102450088174613 58944384145427347883185)
                ·
                  rfl

theorem cell21_774858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 6].length) (baseStart_774858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_774858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_774858 prefixEnd_774858 := by exact prefixLift 774858
  have htrace : WordTrace (prefixWord ++ tailWord_774858) baseStart_774858 baseEnd_774858 := by
    simpa [prefixWord, tailWord_774858, baseEnd_774858] using wordTrace_append hprefix tailTrace_774858
  have hstable : (prefixWord ++ tailWord_774858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774858).length < 2 ^ (prefixWord ++ tailWord_774858).sum := by decide
  have hdescent : baseEnd_774858 < baseStart_774858 := by decide
  rcases family_descends (prefixWord ++ tailWord_774858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774872 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 7]
def baseStart_774872 : Nat := 118140960795 + 774872 * 2 ^ 59
def prefixEnd_774872 : Nat := 4983230072969 + 3 ^ 40 * 774872 * 2
def baseEnd_774872 : Nat := 176836347427021130416193

theorem tailTrace_774872 : CollatzResearch.WordTrace tailWord_774872 prefixEnd_774872 176836347427021130416193 := by
  unfold tailWord_774872
  simp only [CollatzResearch.WordTrace]
  refine ⟨14130951824389278223387435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18841269099185704297849913 14130951824389278223387435)
  ·
    refine ⟨21196427736583917335081153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14130951824389278223387435 21196427736583917335081153)
    ·
      refine ⟨15897320802437938001310865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21196427736583917335081153 15897320802437938001310865)
      ·
        refine ⟨11922990601828453500983149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15897320802437938001310865 11922990601828453500983149)
        ·
          refine ⟨4471121475685670062868681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11922990601828453500983149 4471121475685670062868681)
          ·
            refine ⟨3353341106764252547151511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4471121475685670062868681 3353341106764252547151511)
            ·
              refine ⟨5030011660146378820727267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3353341106764252547151511 5030011660146378820727267)
              ·
                refine ⟨7545017490219568231090901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5030011660146378820727267 7545017490219568231090901)
                ·
                  refine ⟨176836347427021130416193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7545017490219568231090901 176836347427021130416193)
                  ·
                    rfl

theorem cell21_774872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 7].length) (baseStart_774872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_774872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_774872 prefixEnd_774872 := by exact prefixLift 774872
  have htrace : WordTrace (prefixWord ++ tailWord_774872) baseStart_774872 baseEnd_774872 := by
    simpa [prefixWord, tailWord_774872, baseEnd_774872] using wordTrace_append hprefix tailTrace_774872
  have hstable : (prefixWord ++ tailWord_774872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774872).length < 2 ^ (prefixWord ++ tailWord_774872).sum := by decide
  have hdescent : baseEnd_774872 < baseStart_774872 := by decide
  rcases family_descends (prefixWord ++ tailWord_774872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774889 : List Nat := [1, 2, 1, 1, 1, 2, 5, 5, 3]
def baseStart_774889 : Nat := 118140960795 + 774889 * 2 ^ 59
def prefixEnd_774889 : Nat := 4983230072969 + 3 ^ 40 * 774889 * 2
def baseEnd_774889 : Nat := 176840227058632878632825

theorem tailTrace_774889 : CollatzResearch.WordTrace tailWord_774889 prefixEnd_774889 176840227058632878632825 := by
  unfold tailWord_774889
  simp only [CollatzResearch.WordTrace]
  refine ⟨28262523689716968350143721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18841682459811312233429147 28262523689716968350143721)
  ·
    refine ⟨21196892767287726262607791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28262523689716968350143721 21196892767287726262607791)
    ·
      refine ⟨31795339150931589393911687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21196892767287726262607791 31795339150931589393911687)
      ·
        refine ⟨47693008726397384090867531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31795339150931589393911687 47693008726397384090867531)
        ·
          refine ⟨71539513089596076136301297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47693008726397384090867531 71539513089596076136301297)
          ·
            refine ⟨53654634817197057102225973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71539513089596076136301297 53654634817197057102225973)
            ·
              refine ⟨5030122014112224103333685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53654634817197057102225973 5030122014112224103333685)
              ·
                refine ⟨471573938823021009687533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5030122014112224103333685 471573938823021009687533)
                ·
                  refine ⟨176840227058632878632825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 471573938823021009687533 176840227058632878632825)
                  ·
                    rfl

theorem cell21_774889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 5, 3].length) (baseStart_774889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_774889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_774889 prefixEnd_774889 := by exact prefixLift 774889
  have htrace : WordTrace (prefixWord ++ tailWord_774889) baseStart_774889 baseEnd_774889 := by
    simpa [prefixWord, tailWord_774889, baseEnd_774889] using wordTrace_append hprefix tailTrace_774889
  have hstable : (prefixWord ++ tailWord_774889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774889).length < 2 ^ (prefixWord ++ tailWord_774889).sum := by decide
  have hdescent : baseEnd_774889 < baseStart_774889 := by decide
  rcases family_descends (prefixWord ++ tailWord_774889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774957 : List Nat := [1, 5, 3, 2, 1, 1, 3, 2, 3]
def baseStart_774957 : Nat := 118140960795 + 774957 * 2 ^ 59
def prefixEnd_774957 : Nat := 4983230072969 + 3 ^ 40 * 774957 * 2
def baseEnd_774957 : Nat := 176855745585079871499353

theorem tailTrace_774957 : CollatzResearch.WordTrace tailWord_774957 prefixEnd_774957 176855745585079871499353 := by
  unfold tailWord_774957
  simp only [CollatzResearch.WordTrace]
  refine ⟨28265003853470615963619125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18843335902313743975746083 28265003853470615963619125)
  ·
    refine ⟨2649844111262870246589293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28265003853470615963619125 2649844111262870246589293)
    ·
      refine ⟨993691541723576342470985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2649844111262870246589293 993691541723576342470985)
      ·
        refine ⟨745268656292682256853239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 993691541723576342470985 745268656292682256853239)
        ·
          refine ⟨1117902984439023385279859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745268656292682256853239 1117902984439023385279859)
          ·
            refine ⟨1676854476658535077919789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1117902984439023385279859 1676854476658535077919789)
            ·
              refine ⟨628820428746950654219921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1676854476658535077919789 628820428746950654219921)
              ·
                refine ⟨471615321560212990664941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 628820428746950654219921 471615321560212990664941)
                ·
                  refine ⟨176855745585079871499353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 471615321560212990664941 176855745585079871499353)
                  ·
                    rfl

theorem cell21_774957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_774957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_774957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_774957 prefixEnd_774957 := by exact prefixLift 774957
  have htrace : WordTrace (prefixWord ++ tailWord_774957) baseStart_774957 baseEnd_774957 := by
    simpa [prefixWord, tailWord_774957, baseEnd_774957] using wordTrace_append hprefix tailTrace_774957
  have hstable : (prefixWord ++ tailWord_774957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774957).length < 2 ^ (prefixWord ++ tailWord_774957).sum := by decide
  have hdescent : baseEnd_774957 < baseStart_774957 := by decide
  rcases family_descends (prefixWord ++ tailWord_774957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774965 : List Nat := [1, 3, 3, 1, 3, 1, 3, 1, 5]
def baseStart_774965 : Nat := 118140960795 + 774965 * 2 ^ 59
def prefixEnd_774965 : Nat := 4983230072969 + 3 ^ 40 * 774965 * 2
def baseEnd_774965 : Nat := 176857571294073635366003

theorem tailTrace_774965 : CollatzResearch.WordTrace tailWord_774965 prefixEnd_774965 176857571294073635366003 := by
  unfold tailWord_774965
  simp only [CollatzResearch.WordTrace]
  refine ⟨28265295637441633329910349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18843530424961088886606899 28265295637441633329910349)
  ·
    refine ⟨10599485864040612498716381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28265295637441633329910349 10599485864040612498716381)
    ·
      refine ⟨3974807199015229687018643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10599485864040612498716381 3974807199015229687018643)
      ·
        refine ⟨5962210798522844530527965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3974807199015229687018643 5962210798522844530527965)
        ·
          refine ⟨2235829049446066698947987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5962210798522844530527965 2235829049446066698947987)
          ·
            refine ⟨3353743574169100048421981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235829049446066698947987 3353743574169100048421981)
            ·
              refine ⟨1257653840313412518158243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3353743574169100048421981 1257653840313412518158243)
              ·
                refine ⟨1886480760470118777237365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1257653840313412518158243 1886480760470118777237365)
                ·
                  refine ⟨176857571294073635366003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1886480760470118777237365 176857571294073635366003)
                  ·
                    rfl

theorem cell21_774965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_774965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_774965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_774965 prefixEnd_774965 := by exact prefixLift 774965
  have htrace : WordTrace (prefixWord ++ tailWord_774965) baseStart_774965 baseEnd_774965 := by
    simpa [prefixWord, tailWord_774965, baseEnd_774965] using wordTrace_append hprefix tailTrace_774965
  have hstable : (prefixWord ++ tailWord_774965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774965).length < 2 ^ (prefixWord ++ tailWord_774965).sum := by decide
  have hdescent : baseEnd_774965 < baseStart_774965 := by decide
  rcases family_descends (prefixWord ++ tailWord_774965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774979 : List Nat := [1, 1, 1, 3, 1, 4, 3, 3, 4]
def baseStart_774979 : Nat := 118140960795 + 774979 * 2 ^ 59
def prefixEnd_774979 : Nat := 4983230072969 + 3 ^ 40 * 774979 * 2
def baseEnd_774979 : Nat := 176860766284812722132641

theorem tailTrace_774979 : CollatzResearch.WordTrace tailWord_774979 prefixEnd_774979 176860766284812722132641 := by
  unfold tailWord_774979
  simp only [CollatzResearch.WordTrace]
  refine ⟨28265806259390913720919991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18843870839593942480613327 28265806259390913720919991)
  ·
    refine ⟨42398709389086370581379987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28265806259390913720919991 42398709389086370581379987)
    ·
      refine ⟨63598064083629555872069981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42398709389086370581379987 63598064083629555872069981)
      ·
        refine ⟨23849274031361083452026243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63598064083629555872069981 23849274031361083452026243)
        ·
          refine ⟨35773911047041625178039365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23849274031361083452026243 35773911047041625178039365)
          ·
            refine ⟨6707608321320304720882381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35773911047041625178039365 6707608321320304720882381)
            ·
              refine ⟨2515353120495114270330893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6707608321320304720882381 2515353120495114270330893)
              ·
                refine ⟨943257420185667851374085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2515353120495114270330893 943257420185667851374085)
                ·
                  refine ⟨176860766284812722132641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 943257420185667851374085 176860766284812722132641)
                  ·
                    rfl

theorem cell21_774979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 4].length) (baseStart_774979 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_774979 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_774979 prefixEnd_774979 := by exact prefixLift 774979
  have htrace : WordTrace (prefixWord ++ tailWord_774979) baseStart_774979 baseEnd_774979 := by
    simpa [prefixWord, tailWord_774979, baseEnd_774979] using wordTrace_append hprefix tailTrace_774979
  have hstable : (prefixWord ++ tailWord_774979).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774979).length < 2 ^ (prefixWord ++ tailWord_774979).sum := by decide
  have hdescent : baseEnd_774979 < baseStart_774979 := by decide
  rcases family_descends (prefixWord ++ tailWord_774979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775010 : List Nat := [3, 3, 2, 1, 3, 9]
def baseStart_775010 : Nat := 118140960795 + 775010 * 2 ^ 59
def prefixEnd_775010 : Nat := 4983230072969 + 3 ^ 40 * 775010 * 2
def baseEnd_775010 : Nat := 6550660774339391004293

theorem tailTrace_775010 : CollatzResearch.WordTrace tailWord_775010 prefixEnd_775010 6550660774339391004293 := by
  unfold tailWord_775010
  simp only [CollatzResearch.WordTrace]
  refine ⟨7066734230569651503824621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18844624614852404010198989 7066734230569651503824621)
  ·
    refine ⟨2650025336463619313934233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7066734230569651503824621 2650025336463619313934233)
    ·
      refine ⟨1987519002347714485450675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2650025336463619313934233 1987519002347714485450675)
      ·
        refine ⟨2981278503521571728176013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1987519002347714485450675 2981278503521571728176013)
        ·
          refine ⟨1117979438820589398066005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2981278503521571728176013 1117979438820589398066005)
          ·
            refine ⟨6550660774339391004293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1117979438820589398066005 6550660774339391004293)
            ·
              rfl

theorem cell21_775010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 9].length) (baseStart_775010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_775010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_775010 prefixEnd_775010 := by exact prefixLift 775010
  have htrace : WordTrace (prefixWord ++ tailWord_775010) baseStart_775010 baseEnd_775010 := by
    simpa [prefixWord, tailWord_775010, baseEnd_775010] using wordTrace_append hprefix tailTrace_775010
  have hstable : (prefixWord ++ tailWord_775010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775010).length < 2 ^ (prefixWord ++ tailWord_775010).sum := by decide
  have hdescent : baseEnd_775010 < baseStart_775010 := by decide
  rcases family_descends (prefixWord ++ tailWord_775010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775069 : List Nat := [1, 4, 2, 1, 2, 1, 10]
def baseStart_775069 : Nat := 118140960795 + 775069 * 2 ^ 59
def prefixEnd_775069 : Nat := 4983230072969 + 3 ^ 40 * 775069 * 2
def baseEnd_775069 : Nat := 19653478390110285070273

theorem tailTrace_775069 : CollatzResearch.WordTrace tailWord_775069 prefixEnd_775069 19653478390110285070273 := by
  unfold tailWord_775069
  simp only [CollatzResearch.WordTrace]
  refine ⟨28269088829064859091696261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18846059219376572727797507 28269088829064859091696261)
  ·
    refine ⟨5300454155449661079693049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28269088829064859091696261 5300454155449661079693049)
    ·
      refine ⟨3975340616587245809769787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5300454155449661079693049 3975340616587245809769787)
      ·
        refine ⟨5963010924880868714654681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3975340616587245809769787 5963010924880868714654681)
        ·
          refine ⟨4472258193660651535991011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5963010924880868714654681 4472258193660651535991011)
          ·
            refine ⟨6708387290490977303986517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4472258193660651535991011 6708387290490977303986517)
            ·
              refine ⟨19653478390110285070273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6708387290490977303986517 19653478390110285070273)
              ·
                rfl

theorem cell21_775069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 10].length) (baseStart_775069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_775069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_775069 prefixEnd_775069 := by exact prefixLift 775069
  have htrace : WordTrace (prefixWord ++ tailWord_775069) baseStart_775069 baseEnd_775069 := by
    simpa [prefixWord, tailWord_775069, baseEnd_775069] using wordTrace_append hprefix tailTrace_775069
  have hstable : (prefixWord ++ tailWord_775069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775069).length < 2 ^ (prefixWord ++ tailWord_775069).sum := by decide
  have hdescent : baseEnd_775069 < baseStart_775069 := by decide
  rcases family_descends (prefixWord ++ tailWord_775069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775083 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 9]
def baseStart_775083 : Nat := 118140960795 + 775083 * 2 ^ 59
def prefixEnd_775083 : Nat := 4983230072969 + 3 ^ 40 * 775083 * 2
def baseEnd_775083 : Nat := 176884500501731652399095

theorem tailTrace_775083 : CollatzResearch.WordTrace tailWord_775083 prefixEnd_775083 176884500501731652399095 := by
  unfold tailWord_775083
  simp only [CollatzResearch.WordTrace]
  refine ⟨28269599451014139482705903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18846399634009426321803935 28269599451014139482705903)
  ·
    refine ⟨42404399176521209224058855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28269599451014139482705903 42404399176521209224058855)
    ·
      refine ⟨63606598764781813836088283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42404399176521209224058855 63606598764781813836088283)
      ·
        refine ⟨95409898147172720754132425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63606598764781813836088283 95409898147172720754132425)
        ·
          refine ⟨71557423610379540565599319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95409898147172720754132425 71557423610379540565599319)
          ·
            refine ⟨107336135415569310848398979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71557423610379540565599319 107336135415569310848398979)
            ·
              refine ⟨161004203123353966272598469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107336135415569310848398979 161004203123353966272598469)
              ·
                refine ⟨30188288085628868676112213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161004203123353966272598469 30188288085628868676112213)
                ·
                  refine ⟨176884500501731652399095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30188288085628868676112213 176884500501731652399095)
                  ·
                    rfl

theorem cell21_775083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 9].length) (baseStart_775083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_775083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_775083 prefixEnd_775083 := by exact prefixLift 775083
  have htrace : WordTrace (prefixWord ++ tailWord_775083) baseStart_775083 baseEnd_775083 := by
    simpa [prefixWord, tailWord_775083, baseEnd_775083] using wordTrace_append hprefix tailTrace_775083
  have hstable : (prefixWord ++ tailWord_775083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775083).length < 2 ^ (prefixWord ++ tailWord_775083).sum := by decide
  have hdescent : baseEnd_775083 < baseStart_775083 := by decide
  rcases family_descends (prefixWord ++ tailWord_775083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775089 : List Nat := [1, 2, 2, 4, 3, 1, 3, 1, 4]
def baseStart_775089 : Nat := 118140960795 + 775089 * 2 ^ 59
def prefixEnd_775089 : Nat := 4983230072969 + 3 ^ 40 * 775089 * 2
def baseEnd_775089 : Nat := 176885869783476975299083

theorem tailTrace_775089 : CollatzResearch.WordTrace tailWord_775089 prefixEnd_775089 176885869783476975299083 := by
  unfold tailWord_775089
  simp only [CollatzResearch.WordTrace]
  refine ⟨28269818288992402507424321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18846545525994935004949547 28269818288992402507424321)
  ·
    refine ⟨21202363716744301880568241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28269818288992402507424321 21202363716744301880568241)
    ·
      refine ⟨15901772787558226410426181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21202363716744301880568241 15901772787558226410426181)
      ·
        refine ⟨2981582397667167451954909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15901772787558226410426181 2981582397667167451954909)
        ·
          refine ⟨1118093399125187794483091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2981582397667167451954909 1118093399125187794483091)
          ·
            refine ⟨1677140098687781691724637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1118093399125187794483091 1677140098687781691724637)
            ·
              refine ⟨628927537007918134396739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1677140098687781691724637 628927537007918134396739)
              ·
                refine ⟨943391305511877201595109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 628927537007918134396739 943391305511877201595109)
                ·
                  refine ⟨176885869783476975299083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 943391305511877201595109 176885869783476975299083)
                  ·
                    rfl

theorem cell21_775089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 4].length) (baseStart_775089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_775089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_775089 prefixEnd_775089 := by exact prefixLift 775089
  have htrace : WordTrace (prefixWord ++ tailWord_775089) baseStart_775089 baseEnd_775089 := by
    simpa [prefixWord, tailWord_775089, baseEnd_775089] using wordTrace_append hprefix tailTrace_775089
  have hstable : (prefixWord ++ tailWord_775089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775089).length < 2 ^ (prefixWord ++ tailWord_775089).sum := by decide
  have hdescent : baseEnd_775089 < baseStart_775089 := by decide
  rcases family_descends (prefixWord ++ tailWord_775089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775235 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 7]
def baseStart_775235 : Nat := 118140960795 + 775235 * 2 ^ 59
def prefixEnd_775235 : Nat := 4983230072969 + 3 ^ 40 * 775235 * 2
def baseEnd_775235 : Nat := 176919188972613165865451

theorem tailTrace_775235 : CollatzResearch.WordTrace tailWord_775235 prefixEnd_775235 176919188972613165865451 := by
  unfold tailWord_775235
  simp only [CollatzResearch.WordTrace]
  refine ⟨28275143346463469442239159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18850095564308979628159439 28275143346463469442239159)
  ·
    refine ⟨42412715019695204163358739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28275143346463469442239159 42412715019695204163358739)
    ·
      refine ⟨63619072529542806245038109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42412715019695204163358739 63619072529542806245038109)
      ·
        refine ⟨23857152198578552341889291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63619072529542806245038109 23857152198578552341889291)
        ·
          refine ⟨35785728297867828512833937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23857152198578552341889291 35785728297867828512833937)
          ·
            refine ⟨26839296223400871384625453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35785728297867828512833937 26839296223400871384625453)
            ·
              refine ⟨10064736083775326769234545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26839296223400871384625453 10064736083775326769234545)
              ·
                refine ⟨7548552062831495076925909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10064736083775326769234545 7548552062831495076925909)
                ·
                  refine ⟨176919188972613165865451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7548552062831495076925909 176919188972613165865451)
                  ·
                    rfl

theorem cell21_775235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 7].length) (baseStart_775235 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_775235 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_775235 prefixEnd_775235 := by exact prefixLift 775235
  have htrace : WordTrace (prefixWord ++ tailWord_775235) baseStart_775235 baseEnd_775235 := by
    simpa [prefixWord, tailWord_775235, baseEnd_775235] using wordTrace_append hprefix tailTrace_775235
  have hstable : (prefixWord ++ tailWord_775235).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775235).length < 2 ^ (prefixWord ++ tailWord_775235).sum := by decide
  have hdescent : baseEnd_775235 < baseStart_775235 := by decide
  rcases family_descends (prefixWord ++ tailWord_775235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775252 : List Nat := [2, 4, 1, 1, 1, 1, 3, 3, 5]
def baseStart_775252 : Nat := 118140960795 + 775252 * 2 ^ 59
def prefixEnd_775252 : Nat := 4983230072969 + 3 ^ 40 * 775252 * 2
def baseEnd_775252 : Nat := 176923068604224914082083

theorem tailTrace_775252 : CollatzResearch.WordTrace tailWord_775252 prefixEnd_775252 176923068604224914082083 := by
  unfold tailWord_775252
  simp only [CollatzResearch.WordTrace]
  refine ⟨14137881693700940672804005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18850508924934587563738673 14137881693700940672804005)
  ·
    refine ⟨2650852817568926376150751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14137881693700940672804005 2650852817568926376150751)
    ·
      refine ⟨3976279226353389564226127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2650852817568926376150751 3976279226353389564226127)
      ·
        refine ⟨5964418839530084346339191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3976279226353389564226127 5964418839530084346339191)
        ·
          refine ⟨8946628259295126519508787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5964418839530084346339191 8946628259295126519508787)
          ·
            refine ⟨13419942388942689779263181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8946628259295126519508787 13419942388942689779263181)
            ·
              refine ⟨5032478395853508667223693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13419942388942689779263181 5032478395853508667223693)
              ·
                refine ⟨1887179398445065750208885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5032478395853508667223693 1887179398445065750208885)
                ·
                  refine ⟨176923068604224914082083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1887179398445065750208885 176923068604224914082083)
                  ·
                    rfl

theorem cell21_775252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_775252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_775252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_775252 prefixEnd_775252 := by exact prefixLift 775252
  have htrace : WordTrace (prefixWord ++ tailWord_775252) baseStart_775252 baseEnd_775252 := by
    simpa [prefixWord, tailWord_775252, baseEnd_775252] using wordTrace_append hprefix tailTrace_775252
  have hstable : (prefixWord ++ tailWord_775252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775252).length < 2 ^ (prefixWord ++ tailWord_775252).sum := by decide
  have hdescent : baseEnd_775252 < baseStart_775252 := by decide
  rcases family_descends (prefixWord ++ tailWord_775252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775272 : List Nat := [2, 1, 4, 4, 1, 2, 2, 5]
def baseStart_775272 : Nat := 118140960795 + 775272 * 2 ^ 59
def prefixEnd_775272 : Nat := 4983230072969 + 3 ^ 40 * 775272 * 2
def baseEnd_775272 : Nat := 58975877625569774582903

theorem tailTrace_775272 : CollatzResearch.WordTrace tailWord_775272 prefixEnd_775272 58975877625569774582903 := by
  unfold tailWord_775272
  simp only [CollatzResearch.WordTrace]
  refine ⟨14138246423664712380668035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18850995231552949840890713 14138246423664712380668035)
  ·
    refine ⟨21207369635497068571002053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14138246423664712380668035 21207369635497068571002053)
    ·
      refine ⟨3976381806655700357062885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21207369635497068571002053 3976381806655700357062885)
      ·
        refine ⟨745571588747943816949291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3976381806655700357062885 745571588747943816949291)
        ·
          refine ⟨1118357383121915725423937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745571588747943816949291 1118357383121915725423937)
          ·
            refine ⟨838768037341436794067953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1118357383121915725423937 838768037341436794067953)
            ·
              refine ⟨629076028006077595550965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 838768037341436794067953 629076028006077595550965)
              ·
                refine ⟨58975877625569774582903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 629076028006077595550965 58975877625569774582903)
                ·
                  rfl

theorem cell21_775272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 5].length) (baseStart_775272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_775272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_775272 prefixEnd_775272 := by exact prefixLift 775272
  have htrace : WordTrace (prefixWord ++ tailWord_775272) baseStart_775272 baseEnd_775272 := by
    simpa [prefixWord, tailWord_775272, baseEnd_775272] using wordTrace_append hprefix tailTrace_775272
  have hstable : (prefixWord ++ tailWord_775272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775272).length < 2 ^ (prefixWord ++ tailWord_775272).sum := by decide
  have hdescent : baseEnd_775272 < baseStart_775272 := by decide
  rcases family_descends (prefixWord ++ tailWord_775272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775297 : List Nat := [1, 2, 4, 2, 2, 1, 9]
def baseStart_775297 : Nat := 118140960795 + 775297 * 2 ^ 59
def prefixEnd_775297 : Nat := 4983230072969 + 3 ^ 40 * 775297 * 2
def baseEnd_775297 : Nat := 19659259801923870647999

theorem tailTrace_775297 : CollatzResearch.WordTrace tailWord_775297 prefixEnd_775297 19659259801923870647999 := by
  unfold tailWord_775297
  simp only [CollatzResearch.WordTrace]
  refine ⟨28277404672238854030996145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18851603114825902687330763 28277404672238854030996145)
  ·
    refine ⟨21208053504179140523247109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28277404672238854030996145 21208053504179140523247109)
    ·
      refine ⟨3976510032033588848108833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21208053504179140523247109 3976510032033588848108833)
      ·
        refine ⟨2982382524025191636081625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3976510032033588848108833 2982382524025191636081625)
        ·
          refine ⟨2236786893018893727061219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2982382524025191636081625 2236786893018893727061219)
          ·
            refine ⟨3355180339528340590591829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2236786893018893727061219 3355180339528340590591829)
            ·
              refine ⟨19659259801923870647999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3355180339528340590591829 19659259801923870647999)
              ·
                rfl

theorem cell21_775297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 9].length) (baseStart_775297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_775297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_775297 prefixEnd_775297 := by exact prefixLift 775297
  have htrace : WordTrace (prefixWord ++ tailWord_775297) baseStart_775297 baseEnd_775297 := by
    simpa [prefixWord, tailWord_775297, baseEnd_775297] using wordTrace_append hprefix tailTrace_775297
  have hstable : (prefixWord ++ tailWord_775297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775297).length < 2 ^ (prefixWord ++ tailWord_775297).sum := by decide
  have hdescent : baseEnd_775297 < baseStart_775297 := by decide
  rcases family_descends (prefixWord ++ tailWord_775297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775314 : List Nat := [3, 2, 3, 1, 1, 3, 2, 6]
def baseStart_775314 : Nat := 118140960795 + 775314 * 2 ^ 59
def prefixEnd_775314 : Nat := 4983230072969 + 3 ^ 40 * 775314 * 2
def baseEnd_775314 : Nat := 58979072616308861349541

theorem tailTrace_775314 : CollatzResearch.WordTrace tailWord_775314 prefixEnd_775314 58979072616308861349541 := by
  unfold tailWord_775314
  simp only [CollatzResearch.WordTrace]
  refine ⟨7069506178294316483591249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18852016475451510622909997 7069506178294316483591249)
  ·
    refine ⟨5302129633720737362693437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7069506178294316483591249 5302129633720737362693437)
    ·
      refine ⟨1988298612645276511010039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5302129633720737362693437 1988298612645276511010039)
      ·
        refine ⟨2982447918967914766515059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1988298612645276511010039 2982447918967914766515059)
        ·
          refine ⟨4473671878451872149772589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2982447918967914766515059 4473671878451872149772589)
          ·
            refine ⟨1677626954419452056164721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4473671878451872149772589 1677626954419452056164721)
            ·
              refine ⟨1258220215814589042123541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1677626954419452056164721 1258220215814589042123541)
              ·
                refine ⟨58979072616308861349541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1258220215814589042123541 58979072616308861349541)
                ·
                  rfl

theorem cell21_775314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 6].length) (baseStart_775314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_775314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_775314 prefixEnd_775314 := by exact prefixLift 775314
  have htrace : WordTrace (prefixWord ++ tailWord_775314) baseStart_775314 baseEnd_775314 := by
    simpa [prefixWord, tailWord_775314, baseEnd_775314] using wordTrace_append hprefix tailTrace_775314
  have hstable : (prefixWord ++ tailWord_775314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775314).length < 2 ^ (prefixWord ++ tailWord_775314).sum := by decide
  have hdescent : baseEnd_775314 < baseStart_775314 := by decide
  rcases family_descends (prefixWord ++ tailWord_775314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775418 : List Nat := [3, 1, 1, 1, 1, 4, 3, 1, 6]
def baseStart_775418 : Nat := 118140960795 + 775418 * 2 ^ 59
def prefixEnd_775418 : Nat := 4983230072969 + 3 ^ 40 * 775418 * 2
def baseEnd_775418 : Nat := 176960952065845514315077

theorem tailTrace_775418 : CollatzResearch.WordTrace tailWord_775418 prefixEnd_775418 176960952065845514315077 := by
  unfold tailWord_775418
  simp only [CollatzResearch.WordTrace]
  refine ⟨7070454476200122924037727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18854545269866994464100605 7070454476200122924037727)
  ·
    refine ⟨10605681714300184386056591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7070454476200122924037727 10605681714300184386056591)
    ·
      refine ⟨15908522571450276579084887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10605681714300184386056591 15908522571450276579084887)
      ·
        refine ⟨23862783857175414868627331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15908522571450276579084887 23862783857175414868627331)
        ·
          refine ⟨35794175785763122302940997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23862783857175414868627331 35794175785763122302940997)
          ·
            refine ⟨6711407959830585431801437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35794175785763122302940997 6711407959830585431801437)
            ·
              refine ⟨2516777984936469536925539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6711407959830585431801437 2516777984936469536925539)
              ·
                refine ⟨3775166977404704305388309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2516777984936469536925539 3775166977404704305388309)
                ·
                  refine ⟨176960952065845514315077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3775166977404704305388309 176960952065845514315077)
                  ·
                    rfl

theorem cell21_775418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_775418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_775418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_775418 prefixEnd_775418 := by exact prefixLift 775418
  have htrace : WordTrace (prefixWord ++ tailWord_775418) baseStart_775418 baseEnd_775418 := by
    simpa [prefixWord, tailWord_775418, baseEnd_775418] using wordTrace_append hprefix tailTrace_775418
  have hstable : (prefixWord ++ tailWord_775418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775418).length < 2 ^ (prefixWord ++ tailWord_775418).sum := by decide
  have hdescent : baseEnd_775418 < baseStart_775418 := by decide
  rcases family_descends (prefixWord ++ tailWord_775418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775455 : List Nat := [1, 1, 2, 4, 5, 1, 1, 3, 3]
def baseStart_775455 : Nat := 118140960795 + 775455 * 2 ^ 59
def prefixEnd_775455 : Nat := 4983230072969 + 3 ^ 40 * 775455 * 2
def baseEnd_775455 : Nat := 176969395969941672198335

theorem tailTrace_775455 : CollatzResearch.WordTrace tailWord_775455 prefixEnd_775455 176969395969941672198335 := by
  unfold tailWord_775455
  simp only [CollatzResearch.WordTrace]
  refine ⟨28283167405666447015247819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18855444937110964676831879 28283167405666447015247819)
  ·
    refine ⟨42424751108499670522871729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28283167405666447015247819 42424751108499670522871729)
    ·
      refine ⟨31818563331374752892153797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42424751108499670522871729 31818563331374752892153797)
      ·
        refine ⟨5965980624632766167278837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31818563331374752892153797 5965980624632766167278837)
        ·
          refine ⟨559310683559321828182391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5965980624632766167278837 559310683559321828182391)
          ·
            refine ⟨838966025338982742273587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559310683559321828182391 838966025338982742273587)
            ·
              refine ⟨1258449038008474113410381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 838966025338982742273587 1258449038008474113410381)
              ·
                refine ⟨471918389253177792528893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1258449038008474113410381 471918389253177792528893)
                ·
                  refine ⟨176969395969941672198335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 471918389253177792528893 176969395969941672198335)
                  ·
                    rfl

theorem cell21_775455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 3, 3].length) (baseStart_775455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_775455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_775455 prefixEnd_775455 := by exact prefixLift 775455
  have htrace : WordTrace (prefixWord ++ tailWord_775455) baseStart_775455 baseEnd_775455 := by
    simpa [prefixWord, tailWord_775455, baseEnd_775455] using wordTrace_append hprefix tailTrace_775455
  have hstable : (prefixWord ++ tailWord_775455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775455).length < 2 ^ (prefixWord ++ tailWord_775455).sum := by decide
  have hdescent : baseEnd_775455 < baseStart_775455 := by decide
  rcases family_descends (prefixWord ++ tailWord_775455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775466 : List Nat := [3, 1, 4, 2, 1, 3, 7]
def baseStart_775466 : Nat := 118140960795 + 775466 * 2 ^ 59
def prefixEnd_775466 : Nat := 4983230072969 + 3 ^ 40 * 775466 * 2
def baseEnd_775466 : Nat := 19663545146645344168331

theorem tailTrace_775466 : CollatzResearch.WordTrace tailWord_775466 prefixEnd_775466 19663545146645344168331 := by
  unfold tailWord_775466
  simp only [CollatzResearch.WordTrace]
  refine ⟨7070892152156648973474563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18855712405751063929265501 7070892152156648973474563)
  ·
    refine ⟨10606338228234973460211845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7070892152156648973474563 10606338228234973460211845)
    ·
      refine ⟨1988688417794057523789721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10606338228234973460211845 1988688417794057523789721)
      ·
        refine ⟨1491516313345543142842291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1988688417794057523789721 1491516313345543142842291)
        ·
          refine ⟨2237274470018314714263437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1491516313345543142842291 2237274470018314714263437)
          ·
            refine ⟨838977926256868017848789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2237274470018314714263437 838977926256868017848789)
            ·
              refine ⟨19663545146645344168331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 838977926256868017848789 19663545146645344168331)
              ·
                rfl

theorem cell21_775466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 7].length) (baseStart_775466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_775466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_775466 prefixEnd_775466 := by exact prefixLift 775466
  have htrace : WordTrace (prefixWord ++ tailWord_775466) baseStart_775466 baseEnd_775466 := by
    simpa [prefixWord, tailWord_775466, baseEnd_775466] using wordTrace_append hprefix tailTrace_775466
  have hstable : (prefixWord ++ tailWord_775466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775466).length < 2 ^ (prefixWord ++ tailWord_775466).sum := by decide
  have hdescent : baseEnd_775466 < baseStart_775466 := by decide
  rcases family_descends (prefixWord ++ tailWord_775466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775528 : List Nat := [2, 1, 4, 2, 3, 1, 2, 2, 4]
def baseStart_775528 : Nat := 118140960795 + 775528 * 2 ^ 59
def prefixEnd_775528 : Nat := 4983230072969 + 3 ^ 40 * 775528 * 2
def baseEnd_775528 : Nat := 176986055564509767481519

theorem tailTrace_775528 : CollatzResearch.WordTrace tailWord_775528 prefixEnd_775528 176986055564509767481519 := by
  unfold tailWord_775528
  simp only [CollatzResearch.WordTrace]
  refine ⟨14142914967200990241327619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18857219956267986988436825 14142914967200990241327619)
  ·
    refine ⟨21214372450801485361991429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14142914967200990241327619 21214372450801485361991429)
    ·
      refine ⟨3977694834525278505373393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21214372450801485361991429 3977694834525278505373393)
      ·
        refine ⟨2983271125893958879030045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3977694834525278505373393 2983271125893958879030045)
        ·
          refine ⟨1118726672210234579636267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2983271125893958879030045 1118726672210234579636267)
          ·
            refine ⟨1678090008315351869454401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1118726672210234579636267 1678090008315351869454401)
            ·
              refine ⟨1258567506236513902090801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1678090008315351869454401 1258567506236513902090801)
              ·
                refine ⟨943925629677385426568101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1258567506236513902090801 943925629677385426568101)
                ·
                  refine ⟨176986055564509767481519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 943925629677385426568101 176986055564509767481519)
                  ·
                    rfl

theorem cell21_775528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 4].length) (baseStart_775528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_775528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_775528 prefixEnd_775528 := by exact prefixLift 775528
  have htrace : WordTrace (prefixWord ++ tailWord_775528) baseStart_775528 baseEnd_775528 := by
    simpa [prefixWord, tailWord_775528, baseEnd_775528] using wordTrace_append hprefix tailTrace_775528
  have hstable : (prefixWord ++ tailWord_775528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775528).length < 2 ^ (prefixWord ++ tailWord_775528).sum := by decide
  have hdescent : baseEnd_775528 < baseStart_775528 := by decide
  rcases family_descends (prefixWord ++ tailWord_775528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775556 : List Nat := [2, 3, 2, 1, 1, 4, 1, 2, 5]
def baseStart_775556 : Nat := 118140960795 + 775556 * 2 ^ 59
def prefixEnd_775556 : Nat := 4983230072969 + 3 ^ 40 * 775556 * 2
def baseEnd_775556 : Nat := 176992445545987941014795

theorem tailTrace_775556 : CollatzResearch.WordTrace tailWord_775556 prefixEnd_775556 176992445545987941014795 := by
  unfold tailWord_775556
  simp only [CollatzResearch.WordTrace]
  refine ⟨14143425589150270632337261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18857900785533694176449681 14143425589150270632337261)
  ·
    refine ⟨5303784595931351487126473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14143425589150270632337261 5303784595931351487126473)
    ·
      refine ⟨3977838446948513615344855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5303784595931351487126473 3977838446948513615344855)
      ·
        refine ⟨5966757670422770423017283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3977838446948513615344855 5966757670422770423017283)
        ·
          refine ⟨8950136505634155634525925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5966757670422770423017283 8950136505634155634525925)
          ·
            refine ⟨1678150594806404181473611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8950136505634155634525925 1678150594806404181473611)
            ·
              refine ⟨2517225892209606272210417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1678150594806404181473611 2517225892209606272210417)
              ·
                refine ⟨1887919419157204704157813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2517225892209606272210417 1887919419157204704157813)
                ·
                  refine ⟨176992445545987941014795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1887919419157204704157813 176992445545987941014795)
                  ·
                    rfl

theorem cell21_775556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_775556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_775556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_775556 prefixEnd_775556 := by exact prefixLift 775556
  have htrace : WordTrace (prefixWord ++ tailWord_775556) baseStart_775556 baseEnd_775556 := by
    simpa [prefixWord, tailWord_775556, baseEnd_775556] using wordTrace_append hprefix tailTrace_775556
  have hstable : (prefixWord ++ tailWord_775556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775556).length < 2 ^ (prefixWord ++ tailWord_775556).sum := by decide
  have hdescent : baseEnd_775556 < baseStart_775556 := by decide
  rcases family_descends (prefixWord ++ tailWord_775556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775584 : List Nat := [2, 1, 1, 4, 1, 2, 10]
def baseStart_775584 : Nat := 118140960795 + 775584 * 2 ^ 59
def prefixEnd_775584 : Nat := 4983230072969 + 3 ^ 40 * 775584 * 2
def baseEnd_775584 : Nat := 19666537280829568283119

theorem tailTrace_775584 : CollatzResearch.WordTrace tailWord_775584 prefixEnd_775584 19666537280829568283119 := by
  unfold tailWord_775584
  simp only [CollatzResearch.WordTrace]
  refine ⟨14143936211099551023346903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18858581614799401364462537 14143936211099551023346903)
  ·
    refine ⟨21215904316649326535020355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14143936211099551023346903 21215904316649326535020355)
    ·
      refine ⟨31823856474973989802530533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21215904316649326535020355 31823856474973989802530533)
      ·
        refine ⟨5966973089057623087974475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31823856474973989802530533 5966973089057623087974475)
        ·
          refine ⟨8950459633586434631961713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5966973089057623087974475 8950459633586434631961713)
          ·
            refine ⟨6712844725189825973971285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8950459633586434631961713 6712844725189825973971285)
            ·
              refine ⟨19666537280829568283119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6712844725189825973971285 19666537280829568283119)
              ·
                rfl

theorem cell21_775584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 10].length) (baseStart_775584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_775584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_775584 prefixEnd_775584 := by exact prefixLift 775584
  have htrace : WordTrace (prefixWord ++ tailWord_775584) baseStart_775584 baseEnd_775584 := by
    simpa [prefixWord, tailWord_775584, baseEnd_775584] using wordTrace_append hprefix tailTrace_775584
  have hstable : (prefixWord ++ tailWord_775584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775584).length < 2 ^ (prefixWord ++ tailWord_775584).sum := by decide
  have hdescent : baseEnd_775584 < baseStart_775584 := by decide
  rcases family_descends (prefixWord ++ tailWord_775584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775663 : List Nat := [1, 1, 2, 1, 4, 1, 6, 1, 4]
def baseStart_775663 : Nat := 118140960795 + 775663 * 2 ^ 59
def prefixEnd_775663 : Nat := 4983230072969 + 3 ^ 40 * 775663 * 2
def baseEnd_775663 : Nat := 177016864403779532731243

theorem tailTrace_775663 : CollatzResearch.WordTrace tailWord_775663 prefixEnd_775663 177016864403779532731243 := by
  unfold tailWord_775663
  simp only [CollatzResearch.WordTrace]
  refine ⟨28290753788912898538819643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18860502525941932359213095 28290753788912898538819643)
  ·
    refine ⟨42436130683369347808229465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28290753788912898538819643 42436130683369347808229465)
    ·
      refine ⟨31827098012527010856172099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42436130683369347808229465 31827098012527010856172099)
      ·
        refine ⟨47740647018790516284258149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31827098012527010856172099 47740647018790516284258149)
        ·
          refine ⟨8951371316023221803298403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47740647018790516284258149 8951371316023221803298403)
          ·
            refine ⟨13427056974034832704947605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8951371316023221803298403 13427056974034832704947605)
            ·
              refine ⟨629393295657882783044419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13427056974034832704947605 629393295657882783044419)
              ·
                refine ⟨944089943486824174566629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 629393295657882783044419 944089943486824174566629)
                ·
                  refine ⟨177016864403779532731243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 944089943486824174566629 177016864403779532731243)
                  ·
                    rfl

theorem cell21_775663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 4].length) (baseStart_775663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_775663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_775663 prefixEnd_775663 := by exact prefixLift 775663
  have htrace : WordTrace (prefixWord ++ tailWord_775663) baseStart_775663 baseEnd_775663 := by
    simpa [prefixWord, tailWord_775663, baseEnd_775663] using wordTrace_append hprefix tailTrace_775663
  have hstable : (prefixWord ++ tailWord_775663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775663).length < 2 ^ (prefixWord ++ tailWord_775663).sum := by decide
  have hdescent : baseEnd_775663 < baseStart_775663 := by decide
  rcases family_descends (prefixWord ++ tailWord_775663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775700 : List Nat := [2, 4, 3, 1, 2, 2, 2, 2, 3]
def baseStart_775700 : Nat := 118140960795 + 775700 * 2 ^ 59
def prefixEnd_775700 : Nat := 4983230072969 + 3 ^ 40 * 775700 * 2
def baseEnd_775700 : Nat := 177025308307875690614501

theorem tailTrace_775700 : CollatzResearch.WordTrace tailWord_775700 prefixEnd_775700 177025308307875690614501 := by
  unfold tailWord_775700
  simp only [CollatzResearch.WordTrace]
  refine ⟨14146051644889426928958277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18861402193185902571944369 14146051644889426928958277)
  ·
    refine ⟨2652384683416767549179677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14146051644889426928958277 2652384683416767549179677)
    ·
      refine ⟨994644256281287830942379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2652384683416767549179677 994644256281287830942379)
      ·
        refine ⟨1491966384421931746413569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 994644256281287830942379 1491966384421931746413569)
        ·
          refine ⟨1118974788316448809810177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1491966384421931746413569 1118974788316448809810177)
          ·
            refine ⟨839231091237336607357633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1118974788316448809810177 839231091237336607357633)
            ·
              refine ⟨629423318428002455518225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 839231091237336607357633 629423318428002455518225)
              ·
                refine ⟨472067488821001841638669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 629423318428002455518225 472067488821001841638669)
                ·
                  refine ⟨177025308307875690614501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 472067488821001841638669 177025308307875690614501)
                  ·
                    rfl

theorem cell21_775700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_775700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_775700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_775700 prefixEnd_775700 := by exact prefixLift 775700
  have htrace : WordTrace (prefixWord ++ tailWord_775700) baseStart_775700 baseEnd_775700 := by
    simpa [prefixWord, tailWord_775700, baseEnd_775700] using wordTrace_append hprefix tailTrace_775700
  have hstable : (prefixWord ++ tailWord_775700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775700).length < 2 ^ (prefixWord ++ tailWord_775700).sum := by decide
  have hdescent : baseEnd_775700 < baseStart_775700 := by decide
  rcases family_descends (prefixWord ++ tailWord_775700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775767 : List Nat := [1, 1, 3, 2, 2, 3, 1, 3, 5]
def baseStart_775767 : Nat := 118140960795 + 775767 * 2 ^ 59
def prefixEnd_775767 : Nat := 4983230072969 + 3 ^ 40 * 775767 * 2
def baseEnd_775767 : Nat := 177040598620698462997697

theorem tailTrace_775767 : CollatzResearch.WordTrace tailWord_775767 prefixEnd_775767 177040598620698462997697 := by
  unfold tailWord_775767
  simp only [CollatzResearch.WordTrace]
  refine ⟨28294546980536124300605555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18863031320357416200403703 28294546980536124300605555)
  ·
    refine ⟨42441820470804186450908333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28294546980536124300605555 42441820470804186450908333)
    ·
      refine ⟨15915682676551569919090625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42441820470804186450908333 15915682676551569919090625)
      ·
        refine ⟨11936762007413677439317969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15915682676551569919090625 11936762007413677439317969)
        ·
          refine ⟨8952571505560258079488477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11936762007413677439317969 8952571505560258079488477)
          ·
            refine ⟨3357214314585096779808179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8952571505560258079488477 3357214314585096779808179)
            ·
              refine ⟨5035821471877645169712269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3357214314585096779808179 5035821471877645169712269)
              ·
                refine ⟨1888433051954116938642101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5035821471877645169712269 1888433051954116938642101)
                ·
                  refine ⟨177040598620698462997697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1888433051954116938642101 177040598620698462997697)
                  ·
                    rfl

theorem cell21_775767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 5].length) (baseStart_775767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_775767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_775767 prefixEnd_775767 := by exact prefixLift 775767
  have htrace : WordTrace (prefixWord ++ tailWord_775767) baseStart_775767 baseEnd_775767 := by
    simpa [prefixWord, tailWord_775767, baseEnd_775767] using wordTrace_append hprefix tailTrace_775767
  have hstable : (prefixWord ++ tailWord_775767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775767).length < 2 ^ (prefixWord ++ tailWord_775767).sum := by decide
  have hdescent : baseEnd_775767 < baseStart_775767 := by decide
  rcases family_descends (prefixWord ++ tailWord_775767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775784 : List Nat := [2, 1, 4, 3, 1, 1, 2, 2, 5]
def baseStart_775784 : Nat := 118140960795 + 775784 * 2 ^ 59
def prefixEnd_775784 : Nat := 4983230072969 + 3 ^ 40 * 775784 * 2
def baseEnd_775784 : Nat := 177044478252310211214329

theorem tailTrace_775784 : CollatzResearch.WordTrace tailWord_775784 prefixEnd_775784 177044478252310211214329 := by
  unfold tailWord_775784
  simp only [CollatzResearch.WordTrace]
  refine ⟨14147583510737268101987203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18863444680983024135982937 14147583510737268101987203)
  ·
    refine ⟨21221375266105902152980805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14147583510737268101987203 21221375266105902152980805)
    ·
      refine ⟨3979007862394856653683901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21221375266105902152980805 3979007862394856653683901)
      ·
        refine ⟨1492127948398071245131463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3979007862394856653683901 1492127948398071245131463)
        ·
          refine ⟨2238191922597106867697195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1492127948398071245131463 2238191922597106867697195)
          ·
            refine ⟨3357287883895660301545793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2238191922597106867697195 3357287883895660301545793)
            ·
              refine ⟨2517965912921745226159345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3357287883895660301545793 2517965912921745226159345)
              ·
                refine ⟨1888474434691308919619509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2517965912921745226159345 1888474434691308919619509)
                ·
                  refine ⟨177044478252310211214329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1888474434691308919619509 177044478252310211214329)
                  ·
                    rfl

theorem cell21_775784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 5].length) (baseStart_775784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_775784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_775784 prefixEnd_775784 := by exact prefixLift 775784
  have htrace : WordTrace (prefixWord ++ tailWord_775784) baseStart_775784 baseEnd_775784 := by
    simpa [prefixWord, tailWord_775784, baseEnd_775784] using wordTrace_append hprefix tailTrace_775784
  have hstable : (prefixWord ++ tailWord_775784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775784).length < 2 ^ (prefixWord ++ tailWord_775784).sum := by decide
  have hdescent : baseEnd_775784 < baseStart_775784 := by decide
  rcases family_descends (prefixWord ++ tailWord_775784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775818 : List Nat := [3, 1, 2, 3, 2, 2, 3, 2, 3]
def baseStart_775818 : Nat := 118140960795 + 775818 * 2 ^ 59
def prefixEnd_775818 : Nat := 4983230072969 + 3 ^ 40 * 775818 * 2
def baseEnd_775818 : Nat := 177052237515533707647593

theorem tailTrace_775818 : CollatzResearch.WordTrace tailWord_775818 prefixEnd_775818 177052237515533707647593 := by
  unfold tailWord_775818
  simp only [CollatzResearch.WordTrace]
  refine ⟨7074101775837840002678027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18864271402234240007141405 7074101775837840002678027)
  ·
    refine ⟨10611152663756760004017041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7074101775837840002678027 10611152663756760004017041)
    ·
      refine ⟨7958364497817570003012781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10611152663756760004017041 7958364497817570003012781)
      ·
        refine ⟨2984386686681588751129793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7958364497817570003012781 2984386686681588751129793)
        ·
          refine ⟨2238290015011191563347345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2984386686681588751129793 2238290015011191563347345)
          ·
            refine ⟨1678717511258393672510509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2238290015011191563347345 1678717511258393672510509)
            ·
              refine ⟨629519066721897627191441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1678717511258393672510509 629519066721897627191441)
              ·
                refine ⟨472139300041423220393581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 629519066721897627191441 472139300041423220393581)
                ·
                  refine ⟨177052237515533707647593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 472139300041423220393581 177052237515533707647593)
                  ·
                    rfl

theorem cell21_775818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 2, 3].length) (baseStart_775818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_775818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_775818 prefixEnd_775818 := by exact prefixLift 775818
  have htrace : WordTrace (prefixWord ++ tailWord_775818) baseStart_775818 baseEnd_775818 := by
    simpa [prefixWord, tailWord_775818, baseEnd_775818] using wordTrace_append hprefix tailTrace_775818
  have hstable : (prefixWord ++ tailWord_775818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775818).length < 2 ^ (prefixWord ++ tailWord_775818).sum := by decide
  have hdescent : baseEnd_775818 < baseStart_775818 := by decide
  rcases family_descends (prefixWord ++ tailWord_775818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775832 : List Nat := [2, 1, 2, 4, 1, 4, 2, 1, 4]
def baseStart_775832 : Nat := 118140960795 + 775832 * 2 ^ 59
def prefixEnd_775832 : Nat := 4983230072969 + 3 ^ 40 * 775832 * 2
def baseEnd_775832 : Nat := 177055432506272794414231

theorem tailTrace_775832 : CollatzResearch.WordTrace tailWord_775832 prefixEnd_775832 177055432506272794414231 := by
  unfold tailWord_775832
  simp only [CollatzResearch.WordTrace]
  refine ⟨14148458862650320200860875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18864611816867093601147833 14148458862650320200860875)
  ·
    refine ⟨21222688293975480301291313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14148458862650320200860875 21222688293975480301291313)
    ·
      refine ⟨15917016220481610225968485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21222688293975480301291313 15917016220481610225968485)
      ·
        refine ⟨2984440541340301917369091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15917016220481610225968485 2984440541340301917369091)
        ·
          refine ⟨4476660812010452876053637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2984440541340301917369091 4476660812010452876053637)
          ·
            refine ⟨839373902251959914260057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4476660812010452876053637 839373902251959914260057)
            ·
              refine ⟨629530426688969935695043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 839373902251959914260057 629530426688969935695043)
              ·
                refine ⟨944295640033454903542565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 629530426688969935695043 944295640033454903542565)
                ·
                  refine ⟨177055432506272794414231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 944295640033454903542565 177055432506272794414231)
                  ·
                    rfl

theorem cell21_775832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 4].length) (baseStart_775832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_775832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_775832 prefixEnd_775832 := by exact prefixLift 775832
  have htrace : WordTrace (prefixWord ++ tailWord_775832) baseStart_775832 baseEnd_775832 := by
    simpa [prefixWord, tailWord_775832, baseEnd_775832] using wordTrace_append hprefix tailTrace_775832
  have hstable : (prefixWord ++ tailWord_775832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775832).length < 2 ^ (prefixWord ++ tailWord_775832).sum := by decide
  have hdescent : baseEnd_775832 < baseStart_775832 := by decide
  rcases family_descends (prefixWord ++ tailWord_775832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775894 : List Nat := [5, 2, 1, 3, 1, 1, 1, 2, 5]
def baseStart_775894 : Nat := 118140960795 + 775894 * 2 ^ 59
def prefixEnd_775894 : Nat := 4983230072969 + 3 ^ 40 * 775894 * 2
def baseEnd_775894 : Nat := 177069581750974464380771

theorem tailTrace_775894 : CollatzResearch.WordTrace tailWord_775894 prefixEnd_775894 177069581750974464380771 := by
  unfold tailWord_775894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1768698690692251561904921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18866119367384016660319157 1768698690692251561904921)
  ·
    refine ⟨1326524018019188671428691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1768698690692251561904921 1326524018019188671428691)
    ·
      refine ⟨1989786027028783007143037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1326524018019188671428691 1989786027028783007143037)
      ·
        refine ⟨746169760135793627678639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1989786027028783007143037 746169760135793627678639)
        ·
          refine ⟨1119254640203690441517959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 746169760135793627678639 1119254640203690441517959)
          ·
            refine ⟨1678881960305535662276939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1119254640203690441517959 1678881960305535662276939)
            ·
              refine ⟨2518322940458303493415409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1678881960305535662276939 2518322940458303493415409)
              ·
                refine ⟨1888742205343727620061557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2518322940458303493415409 1888742205343727620061557)
                ·
                  refine ⟨177069581750974464380771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1888742205343727620061557 177069581750974464380771)
                  ·
                    rfl

theorem cell21_775894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_775894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_775894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_775894 prefixEnd_775894 := by exact prefixLift 775894
  have htrace : WordTrace (prefixWord ++ tailWord_775894) baseStart_775894 baseEnd_775894 := by
    simpa [prefixWord, tailWord_775894, baseEnd_775894] using wordTrace_append hprefix tailTrace_775894
  have hstable : (prefixWord ++ tailWord_775894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775894).length < 2 ^ (prefixWord ++ tailWord_775894).sum := by decide
  have hdescent : baseEnd_775894 < baseStart_775894 := by decide
  rcases family_descends (prefixWord ++ tailWord_775894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775950 : List Nat := [4, 1, 1, 2, 1, 1, 2, 5, 4]
def baseStart_775950 : Nat := 118140960795 + 775950 * 2 ^ 59
def prefixEnd_775950 : Nat := 4983230072969 + 3 ^ 40 * 775950 * 2
def baseEnd_775950 : Nat := 177082361713930811447323

theorem tailTrace_775950 : CollatzResearch.WordTrace tailWord_775950 prefixEnd_775950 177082361713930811447323 := by
  unfold tailWord_775950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3537652692359143319314663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18867481025915431036344869 3537652692359143319314663)
  ·
    refine ⟨5306479038538714978971995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3537652692359143319314663 5306479038538714978971995)
    ·
      refine ⟨7959718557808072468457993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5306479038538714978971995 7959718557808072468457993)
      ·
        refine ⟨5969788918356054351343495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7959718557808072468457993 5969788918356054351343495)
        ·
          refine ⟨8954683377534081527015243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5969788918356054351343495 8954683377534081527015243)
          ·
            refine ⟨13432025066301122290522865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8954683377534081527015243 13432025066301122290522865)
            ·
              refine ⟨10074018799725841717892149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13432025066301122290522865 10074018799725841717892149)
              ·
                refine ⟨944439262474297661052389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10074018799725841717892149 944439262474297661052389)
                ·
                  refine ⟨177082361713930811447323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 944439262474297661052389 177082361713930811447323)
                  ·
                    rfl

theorem cell21_775950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_775950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_775950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_775950 prefixEnd_775950 := by exact prefixLift 775950
  have htrace : WordTrace (prefixWord ++ tailWord_775950) baseStart_775950 baseEnd_775950 := by
    simpa [prefixWord, tailWord_775950, baseEnd_775950] using wordTrace_append hprefix tailTrace_775950
  have hstable : (prefixWord ++ tailWord_775950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775950).length < 2 ^ (prefixWord ++ tailWord_775950).sum := by decide
  have hdescent : baseEnd_775950 < baseStart_775950 := by decide
  rcases family_descends (prefixWord ++ tailWord_775950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775964 : List Nat := [2, 2, 3, 1, 1, 2, 3, 7]
def baseStart_775964 : Nat := 118140960795 + 775964 * 2 ^ 59
def prefixEnd_775964 : Nat := 4983230072969 + 3 ^ 40 * 775964 * 2
def baseEnd_775964 : Nat := 59028518901556632737987

theorem tailTrace_775964 : CollatzResearch.WordTrace tailWord_775964 prefixEnd_775964 59028518901556632737987 := by
  unfold tailWord_775964
  simp only [CollatzResearch.WordTrace]
  refine ⟨14150866080411213472763473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18867821440548284630351297 14150866080411213472763473)
  ·
    refine ⟨10613149560308410104572605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14150866080411213472763473 10613149560308410104572605)
    ·
      refine ⟨3979931085115653789214727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10613149560308410104572605 3979931085115653789214727)
      ·
        refine ⟨5969896627673480683822091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3979931085115653789214727 5969896627673480683822091)
        ·
          refine ⟨8954844941510221025733137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5969896627673480683822091 8954844941510221025733137)
          ·
            refine ⟨6716133706132665769299853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8954844941510221025733137 6716133706132665769299853)
            ·
              refine ⟨2518550139799749663487445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6716133706132665769299853 2518550139799749663487445)
              ·
                refine ⟨59028518901556632737987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2518550139799749663487445 59028518901556632737987)
                ·
                  rfl

theorem cell21_775964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 7].length) (baseStart_775964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_775964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_775964 prefixEnd_775964 := by exact prefixLift 775964
  have htrace : WordTrace (prefixWord ++ tailWord_775964) baseStart_775964 baseEnd_775964 := by
    simpa [prefixWord, tailWord_775964, baseEnd_775964] using wordTrace_append hprefix tailTrace_775964
  have hstable : (prefixWord ++ tailWord_775964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775964).length < 2 ^ (prefixWord ++ tailWord_775964).sum := by decide
  have hdescent : baseEnd_775964 < baseStart_775964 := by decide
  rcases family_descends (prefixWord ++ tailWord_775964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776046 : List Nat := [4, 1, 2, 3, 1, 1, 4, 2, 3]
def baseStart_776046 : Nat := 118140960795 + 776046 * 2 ^ 59
def prefixEnd_776046 : Nat := 4983230072969 + 3 ^ 40 * 776046 * 2
def baseEnd_776046 : Nat := 177104270221855977847127

theorem tailTrace_776046 : CollatzResearch.WordTrace tailWord_776046 prefixEnd_776046 177104270221855977847127 := by
  unfold tailWord_776046
  simp only [CollatzResearch.WordTrace]
  refine ⟨3538090368315669368751499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18869815297683569966674661 3538090368315669368751499)
  ·
    refine ⟨5307135552473504053127249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3538090368315669368751499 5307135552473504053127249)
    ·
      refine ⟨3980351664355128039845437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5307135552473504053127249 3980351664355128039845437)
      ·
        refine ⟨1492631874133173014942039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3980351664355128039845437 1492631874133173014942039)
        ·
          refine ⟨2238947811199759522413059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1492631874133173014942039 2238947811199759522413059)
          ·
            refine ⟨3358421716799639283619589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2238947811199759522413059 3358421716799639283619589)
            ·
              refine ⟨629704071899932365678673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3358421716799639283619589 629704071899932365678673)
              ·
                refine ⟨472278053924949274259005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 629704071899932365678673 472278053924949274259005)
                ·
                  refine ⟨177104270221855977847127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 472278053924949274259005 177104270221855977847127)
                  ·
                    rfl

theorem cell21_776046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_776046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_776046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_776046 prefixEnd_776046 := by exact prefixLift 776046
  have htrace : WordTrace (prefixWord ++ tailWord_776046) baseStart_776046 baseEnd_776046 := by
    simpa [prefixWord, tailWord_776046, baseEnd_776046] using wordTrace_append hprefix tailTrace_776046
  have hstable : (prefixWord ++ tailWord_776046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776046).length < 2 ^ (prefixWord ++ tailWord_776046).sum := by decide
  have hdescent : baseEnd_776046 < baseStart_776046 := by decide
  rcases family_descends (prefixWord ++ tailWord_776046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776074 : List Nat := [3, 1, 2, 4, 2, 1, 3, 5]
def baseStart_776074 : Nat := 118140960795 + 776074 * 2 ^ 59
def prefixEnd_776074 : Nat := 4983230072969 + 3 ^ 40 * 776074 * 2
def baseEnd_776074 : Nat := 59036886734444717126801

theorem tailTrace_776074 : CollatzResearch.WordTrace tailWord_776074 prefixEnd_776074 59036886734444717126801 := by
  unfold tailWord_776074
  simp only [CollatzResearch.WordTrace]
  refine ⟨7076436047605978933007819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18870496126949277154687517 7076436047605978933007819)
  ·
    refine ⟨10614654071408968399511729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7076436047605978933007819 10614654071408968399511729)
    ·
      refine ⟨7960990553556726299633797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10614654071408968399511729 7960990553556726299633797)
      ·
        refine ⟨1492685728791886181181337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7960990553556726299633797 1492685728791886181181337)
        ·
          refine ⟨1119514296593914635886003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1492685728791886181181337 1119514296593914635886003)
          ·
            refine ⟨1679271444890871953829005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1119514296593914635886003 1679271444890871953829005)
            ·
              refine ⟨629726791834076982685877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1679271444890871953829005 629726791834076982685877)
              ·
                refine ⟨59036886734444717126801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 629726791834076982685877 59036886734444717126801)
                ·
                  rfl

theorem cell21_776074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 5].length) (baseStart_776074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_776074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_776074 prefixEnd_776074 := by exact prefixLift 776074
  have htrace : WordTrace (prefixWord ++ tailWord_776074) baseStart_776074 baseEnd_776074 := by
    simpa [prefixWord, tailWord_776074, baseEnd_776074] using wordTrace_append hprefix tailTrace_776074
  have hstable : (prefixWord ++ tailWord_776074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776074).length < 2 ^ (prefixWord ++ tailWord_776074).sum := by decide
  have hdescent : baseEnd_776074 < baseStart_776074 := by decide
  rcases family_descends (prefixWord ++ tailWord_776074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776085 : List Nat := [1, 3, 2, 1, 1, 3, 2, 2, 6]
def baseStart_776085 : Nat := 118140960795 + 776085 * 2 ^ 59
def prefixEnd_776085 : Nat := 4983230072969 + 3 ^ 40 * 776085 * 2
def baseEnd_776085 : Nat := 177113170553200576697047

theorem tailTrace_776085 : CollatzResearch.WordTrace tailWord_776085 prefixEnd_776085 177113170553200576697047 := by
  unfold tailWord_776085
  simp only [CollatzResearch.WordTrace]
  refine ⟨28306145393384064610681709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18870763595589376407121139 28306145393384064610681709)
  ·
    refine ⟨10614804522519024229005641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28306145393384064610681709 10614804522519024229005641)
    ·
      refine ⟨7961103391889268171754231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10614804522519024229005641 7961103391889268171754231)
      ·
        refine ⟨11941655087833902257631347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7961103391889268171754231 11941655087833902257631347)
        ·
          refine ⟨17912482631750853386447021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11941655087833902257631347 17912482631750853386447021)
          ·
            refine ⟨6717180986906570019917633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17912482631750853386447021 6717180986906570019917633)
            ·
              refine ⟨5037885740179927514938225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6717180986906570019917633 5037885740179927514938225)
              ·
                refine ⟨3778414305134945636203669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5037885740179927514938225 3778414305134945636203669)
                ·
                  refine ⟨177113170553200576697047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3778414305134945636203669 177113170553200576697047)
                  ·
                    rfl

theorem cell21_776085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_776085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_776085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_776085 prefixEnd_776085 := by exact prefixLift 776085
  have htrace : WordTrace (prefixWord ++ tailWord_776085) baseStart_776085 baseEnd_776085 := by
    simpa [prefixWord, tailWord_776085, baseEnd_776085] using wordTrace_append hprefix tailTrace_776085
  have hstable : (prefixWord ++ tailWord_776085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776085).length < 2 ^ (prefixWord ++ tailWord_776085).sum := by decide
  have hdescent : baseEnd_776085 < baseStart_776085 := by decide
  rcases family_descends (prefixWord ++ tailWord_776085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776094 : List Nat := [4, 3, 1, 3, 2, 1, 1, 2, 4]
def baseStart_776094 : Nat := 118140960795 + 776094 * 2 ^ 59
def prefixEnd_776094 : Nat := 4983230072969 + 3 ^ 40 * 776094 * 2
def baseEnd_776094 : Nat := 177115224475818561047029

theorem tailTrace_776094 : CollatzResearch.WordTrace tailWord_776094 prefixEnd_776094 177115224475818561047029 := by
  unfold tailWord_776094
  simp only [CollatzResearch.WordTrace]
  refine ⟨3538309206293932393469917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18870982433567639431839557 3538309206293932393469917)
  ·
    refine ⟨1326865952360224647551219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3538309206293932393469917 1326865952360224647551219)
    ·
      refine ⟨1990298928540336971326829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1326865952360224647551219 1990298928540336971326829)
      ·
        refine ⟨746362098202626364247561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1990298928540336971326829 746362098202626364247561)
        ·
          refine ⟨559771573651969773185671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 746362098202626364247561 559771573651969773185671)
          ·
            refine ⟨839657360477954659778507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559771573651969773185671 839657360477954659778507)
            ·
              refine ⟨1259486040716931989667761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 839657360477954659778507 1259486040716931989667761)
              ·
                refine ⟨944614530537698992250821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1259486040716931989667761 944614530537698992250821)
                ·
                  refine ⟨177115224475818561047029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 944614530537698992250821 177115224475818561047029)
                  ·
                    rfl

theorem cell21_776094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_776094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_776094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_776094 prefixEnd_776094 := by exact prefixLift 776094
  have htrace : WordTrace (prefixWord ++ tailWord_776094) baseStart_776094 baseEnd_776094 := by
    simpa [prefixWord, tailWord_776094, baseEnd_776094] using wordTrace_append hprefix tailTrace_776094
  have hstable : (prefixWord ++ tailWord_776094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776094).length < 2 ^ (prefixWord ++ tailWord_776094).sum := by decide
  have hdescent : baseEnd_776094 < baseStart_776094 := by decide
  rcases family_descends (prefixWord ++ tailWord_776094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776150 : List Nat := [5, 2, 1, 1, 3, 2, 7]
def baseStart_776150 : Nat := 118140960795 + 776150 * 2 ^ 59
def prefixEnd_776150 : Nat := 4983230072969 + 3 ^ 40 * 776150 * 2
def baseEnd_776150 : Nat := 19680889382086100901509

theorem tailTrace_776150 : CollatzResearch.WordTrace tailWord_776150 prefixEnd_776150 19680889382086100901509 := by
  unfold tailWord_776150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1769282258634286294487369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18872344092099053807865269 1769282258634286294487369)
  ·
    refine ⟨1326961693975714720865527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1769282258634286294487369 1326961693975714720865527)
    ·
      refine ⟨1990442540963572081298291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1326961693975714720865527 1990442540963572081298291)
      ·
        refine ⟨2985663811445358121947437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1990442540963572081298291 2985663811445358121947437)
        ·
          refine ⟨1119623929292009295730289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2985663811445358121947437 1119623929292009295730289)
          ·
            refine ⟨839717946969006971797717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1119623929292009295730289 839717946969006971797717)
            ·
              refine ⟨19680889382086100901509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 839717946969006971797717 19680889382086100901509)
              ·
                rfl

theorem cell21_776150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 7].length) (baseStart_776150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_776150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_776150 prefixEnd_776150 := by exact prefixLift 776150
  have htrace : WordTrace (prefixWord ++ tailWord_776150) baseStart_776150 baseEnd_776150 := by
    simpa [prefixWord, tailWord_776150, baseEnd_776150] using wordTrace_append hprefix tailTrace_776150
  have hstable : (prefixWord ++ tailWord_776150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776150).length < 2 ^ (prefixWord ++ tailWord_776150).sum := by decide
  have hdescent : baseEnd_776150 < baseStart_776150 := by decide
  rcases family_descends (prefixWord ++ tailWord_776150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776156 : List Nat := [2, 2, 6, 1, 1, 1, 3, 2, 3]
def baseStart_776156 : Nat := 118140960795 + 776156 * 2 ^ 59
def prefixEnd_776156 : Nat := 4983230072969 + 3 ^ 40 * 776156 * 2
def baseEnd_776156 : Nat := 177129373720520231013569

theorem tailTrace_776156 : CollatzResearch.WordTrace tailWord_776156 prefixEnd_776156 177129373720520231013569 := by
  unfold tailWord_776156
  simp only [CollatzResearch.WordTrace]
  refine ⟨14154367488063421868258161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18872489984084562491010881 14154367488063421868258161)
  ·
    refine ⟨10615775616047566401193621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14154367488063421868258161 10615775616047566401193621)
    ·
      refine ⟨497614482002229675055951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10615775616047566401193621 497614482002229675055951)
      ·
        refine ⟨746421723003344512583927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497614482002229675055951 746421723003344512583927)
        ·
          refine ⟨1119632584505016768875891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 746421723003344512583927 1119632584505016768875891)
          ·
            refine ⟨1679448876757525153313837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1119632584505016768875891 1679448876757525153313837)
            ·
              refine ⟨629793328784071932492689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1679448876757525153313837 629793328784071932492689)
              ·
                refine ⟨472344996588053949369517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 629793328784071932492689 472344996588053949369517)
                ·
                  refine ⟨177129373720520231013569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 472344996588053949369517 177129373720520231013569)
                  ·
                    rfl

theorem cell21_776156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 2, 3].length) (baseStart_776156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_776156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_776156 prefixEnd_776156 := by exact prefixLift 776156
  have htrace : WordTrace (prefixWord ++ tailWord_776156) baseStart_776156 baseEnd_776156 := by
    simpa [prefixWord, tailWord_776156, baseEnd_776156] using wordTrace_append hprefix tailTrace_776156
  have hstable : (prefixWord ++ tailWord_776156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776156).length < 2 ^ (prefixWord ++ tailWord_776156).sum := by decide
  have hdescent : baseEnd_776156 < baseStart_776156 := by decide
  rcases family_descends (prefixWord ++ tailWord_776156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776161 : List Nat := [1, 2, 3, 1, 2, 1, 4, 1, 6]
def baseStart_776161 : Nat := 118140960795 + 776161 * 2 ^ 59
def prefixEnd_776161 : Nat := 4983230072969 + 3 ^ 40 * 776161 * 2
def baseEnd_776161 : Nat := 177130514788641333430225

theorem tailTrace_776161 : CollatzResearch.WordTrace tailWord_776161 prefixEnd_776161 177130514788641333430225 := by
  unfold tailWord_776161
  simp only [CollatzResearch.WordTrace]
  refine ⟨28308917341108729590448337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18872611560739153060298891 28308917341108729590448337)
  ·
    refine ⟨21231688005831547192836253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28308917341108729590448337 21231688005831547192836253)
    ·
      refine ⟨7961883002186830197313595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21231688005831547192836253 7961883002186830197313595)
      ·
        refine ⟨11942824503280245295970393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7961883002186830197313595 11942824503280245295970393)
        ·
          refine ⟨8957118377460183971977795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11942824503280245295970393 8957118377460183971977795)
          ·
            refine ⟨13435677566190275957966693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8957118377460183971977795 13435677566190275957966693)
            ·
              refine ⟨2519189543660676742118755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13435677566190275957966693 2519189543660676742118755)
              ·
                refine ⟨3778784315491015113178133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2519189543660676742118755 3778784315491015113178133)
                ·
                  refine ⟨177130514788641333430225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3778784315491015113178133 177130514788641333430225)
                  ·
                    rfl

theorem cell21_776161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 6].length) (baseStart_776161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_776161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_776161 prefixEnd_776161 := by exact prefixLift 776161
  have htrace : WordTrace (prefixWord ++ tailWord_776161) baseStart_776161 baseEnd_776161 := by
    simpa [prefixWord, tailWord_776161, baseEnd_776161] using wordTrace_append hprefix tailTrace_776161
  have hstable : (prefixWord ++ tailWord_776161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776161).length < 2 ^ (prefixWord ++ tailWord_776161).sum := by decide
  have hdescent : baseEnd_776161 < baseStart_776161 := by decide
  rcases family_descends (prefixWord ++ tailWord_776161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776215 : List Nat := [1, 1, 3, 5, 3, 1, 2, 2, 3]
def baseStart_776215 : Nat := 118140960795 + 776215 * 2 ^ 59
def prefixEnd_776215 : Nat := 4983230072969 + 3 ^ 40 * 776215 * 2
def baseEnd_776215 : Nat := 177142838324349239530115

theorem tailTrace_776215 : CollatzResearch.WordTrace tailWord_776215 prefixEnd_776215 177142838324349239530115 := by
  unfold tailWord_776215
  simp only [CollatzResearch.WordTrace]
  refine ⟨28310886882913096812914099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18873924588608731208609399 28310886882913096812914099)
  ·
    refine ⟨42466330324369645219371149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28310886882913096812914099 42466330324369645219371149)
    ·
      refine ⟨15924873871638616957264181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42466330324369645219371149 15924873871638616957264181)
      ·
        refine ⟨1492956925466120339743517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15924873871638616957264181 1492956925466120339743517)
        ·
          refine ⟨559858847049795127403819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1492956925466120339743517 559858847049795127403819)
          ·
            refine ⟨839788270574692691105729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559858847049795127403819 839788270574692691105729)
            ·
              refine ⟨629841202931019518329297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 839788270574692691105729 629841202931019518329297)
              ·
                refine ⟨472380902198264638746973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 629841202931019518329297 472380902198264638746973)
                ·
                  refine ⟨177142838324349239530115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 472380902198264638746973 177142838324349239530115)
                  ·
                    rfl

theorem cell21_776215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 2, 3].length) (baseStart_776215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_776215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_776215 prefixEnd_776215 := by exact prefixLift 776215
  have htrace : WordTrace (prefixWord ++ tailWord_776215) baseStart_776215 baseEnd_776215 := by
    simpa [prefixWord, tailWord_776215, baseEnd_776215] using wordTrace_append hprefix tailTrace_776215
  have hstable : (prefixWord ++ tailWord_776215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776215).length < 2 ^ (prefixWord ++ tailWord_776215).sum := by decide
  have hdescent : baseEnd_776215 < baseStart_776215 := by decide
  rcases family_descends (prefixWord ++ tailWord_776215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776257 : List Nat := [1, 2, 5, 1, 2, 2, 2, 3, 3]
def baseStart_776257 : Nat := 118140960795 + 776257 * 2 ^ 59
def prefixEnd_776257 : Nat := 4983230072969 + 3 ^ 40 * 776257 * 2
def baseEnd_776257 : Nat := 177152423296566499830029

theorem tailTrace_776257 : CollatzResearch.WordTrace tailWord_776257 prefixEnd_776257 177152423296566499830029 := by
  unfold tailWord_776257
  simp only [CollatzResearch.WordTrace]
  refine ⟨28312418748760937985943025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18874945832507291990628683 28312418748760937985943025)
  ·
    refine ⟨21234314061570703489457269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28312418748760937985943025 21234314061570703489457269)
    ·
      refine ⟨1990716943272253452136619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21234314061570703489457269 1990716943272253452136619)
      ·
        refine ⟨2986075414908380178204929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1990716943272253452136619 2986075414908380178204929)
        ·
          refine ⟨2239556561181285133653697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2986075414908380178204929 2239556561181285133653697)
          ·
            refine ⟨1679667420885963850240273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2239556561181285133653697 1679667420885963850240273)
            ·
              refine ⟨1259750565664472887680205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1679667420885963850240273 1259750565664472887680205)
              ·
                refine ⟨472406462124177332880077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1259750565664472887680205 472406462124177332880077)
                ·
                  refine ⟨177152423296566499830029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 472406462124177332880077 177152423296566499830029)
                  ·
                    rfl

theorem cell21_776257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 3, 3].length) (baseStart_776257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_776257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_776257 prefixEnd_776257 := by exact prefixLift 776257
  have htrace : WordTrace (prefixWord ++ tailWord_776257) baseStart_776257 baseEnd_776257 := by
    simpa [prefixWord, tailWord_776257, baseEnd_776257] using wordTrace_append hprefix tailTrace_776257
  have hstable : (prefixWord ++ tailWord_776257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776257).length < 2 ^ (prefixWord ++ tailWord_776257).sum := by decide
  have hdescent : baseEnd_776257 < baseStart_776257 := by decide
  rcases family_descends (prefixWord ++ tailWord_776257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776313 : List Nat := [1, 2, 1, 3, 4, 1, 1, 2, 6]
def baseStart_776313 : Nat := 118140960795 + 776313 * 2 ^ 59
def prefixEnd_776313 : Nat := 4983230072969 + 3 ^ 40 * 776313 * 2
def baseEnd_776313 : Nat := 177165203259522846896581

theorem tailTrace_776313 : CollatzResearch.WordTrace tailWord_776313 prefixEnd_776313 177165203259522846896581 := by
  unfold tailWord_776313
  simp only [CollatzResearch.WordTrace]
  refine ⟨28314461236558059549981593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18876307491038706366654395 28314461236558059549981593)
  ·
    refine ⟨21235845927418544662486195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28314461236558059549981593 21235845927418544662486195)
    ·
      refine ⟨31853768891127816993729293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21235845927418544662486195 31853768891127816993729293)
      ·
        refine ⟨11945163334172931372648485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31853768891127816993729293 11945163334172931372648485)
        ·
          refine ⟨2239718125157424632371591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11945163334172931372648485 2239718125157424632371591)
          ·
            refine ⟨3359577187736136948557387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2239718125157424632371591 3359577187736136948557387)
            ·
              refine ⟨5039365781604205422836081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3359577187736136948557387 5039365781604205422836081)
              ·
                refine ⟨3779524336203154067127061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5039365781604205422836081 3779524336203154067127061)
                ·
                  refine ⟨177165203259522846896581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3779524336203154067127061 177165203259522846896581)
                  ·
                    rfl

theorem cell21_776313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 6].length) (baseStart_776313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_776313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_776313 prefixEnd_776313 := by exact prefixLift 776313
  have htrace : WordTrace (prefixWord ++ tailWord_776313) baseStart_776313 baseEnd_776313 := by
    simpa [prefixWord, tailWord_776313, baseEnd_776313] using wordTrace_append hprefix tailTrace_776313
  have hstable : (prefixWord ++ tailWord_776313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776313).length < 2 ^ (prefixWord ++ tailWord_776313).sum := by decide
  have hdescent : baseEnd_776313 < baseStart_776313 := by decide
  rcases family_descends (prefixWord ++ tailWord_776313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776316 : List Nat := [2, 2, 2, 1, 1, 4, 3, 3, 3]
def baseStart_776316 : Nat := 118140960795 + 776316 * 2 ^ 59
def prefixEnd_776316 : Nat := 4983230072969 + 3 ^ 40 * 776316 * 2
def baseEnd_776316 : Nat := 177165887900395508346575

theorem tailTrace_776316 : CollatzResearch.WordTrace tailWord_776316 prefixEnd_776316 177165887900395508346575 := by
  unfold tailWord_776316
  simp only [CollatzResearch.WordTrace]
  refine ⟨14157285327773595531170401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18876380437031460708227201 14157285327773595531170401)
  ·
    refine ⟨10617963995830196648377801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14157285327773595531170401 10617963995830196648377801)
    ·
      refine ⟨7963472996872647486283351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10617963995830196648377801 7963472996872647486283351)
      ·
        refine ⟨11945209495308971229425027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7963472996872647486283351 11945209495308971229425027)
        ·
          refine ⟨17917814242963456844137541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11945209495308971229425027 17917814242963456844137541)
          ·
            refine ⟨3359590170555648158275789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17917814242963456844137541 3359590170555648158275789)
            ·
              refine ⟨1259846313958368059353421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3359590170555648158275789 1259846313958368059353421)
              ·
                refine ⟨472442367734388022257533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1259846313958368059353421 472442367734388022257533)
                ·
                  refine ⟨177165887900395508346575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 472442367734388022257533 177165887900395508346575)
                  ·
                    rfl

theorem cell21_776316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 3, 3].length) (baseStart_776316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_776316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_776316 prefixEnd_776316 := by exact prefixLift 776316
  have htrace : WordTrace (prefixWord ++ tailWord_776316) baseStart_776316 baseEnd_776316 := by
    simpa [prefixWord, tailWord_776316, baseEnd_776316] using wordTrace_append hprefix tailTrace_776316
  have hstable : (prefixWord ++ tailWord_776316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776316).length < 2 ^ (prefixWord ++ tailWord_776316).sum := by decide
  have hdescent : baseEnd_776316 < baseStart_776316 := by decide
  rcases family_descends (prefixWord ++ tailWord_776316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776327 : List Nat := [1, 1, 4, 2, 1, 1, 11]
def baseStart_776327 : Nat := 118140960795 + 776327 * 2 ^ 59
def prefixEnd_776327 : Nat := 4983230072969 + 3 ^ 40 * 776327 * 2
def baseEnd_776327 : Nat := 19685377583362437073691

theorem tailTrace_776327 : CollatzResearch.WordTrace tailWord_776327 prefixEnd_776327 19685377583362437073691 := by
  unfold tailWord_776327
  simp only [CollatzResearch.WordTrace]
  refine ⟨28314971858507339940991235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18876647905671559960660823 28314971858507339940991235)
  ·
    refine ⟨42472457787761009911486853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28314971858507339940991235 42472457787761009911486853)
    ·
      refine ⟨7963585835205189358403785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42472457787761009911486853 7963585835205189358403785)
      ·
        refine ⟨5972689376403892018802839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7963585835205189358403785 5972689376403892018802839)
        ·
          refine ⟨8959034064605838028204259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5972689376403892018802839 8959034064605838028204259)
          ·
            refine ⟨13438551096908757042306389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8959034064605838028204259 13438551096908757042306389)
            ·
              refine ⟨19685377583362437073691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 13438551096908757042306389 19685377583362437073691)
              ·
                rfl

theorem cell21_776327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 11].length) (baseStart_776327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_776327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_776327 prefixEnd_776327 := by exact prefixLift 776327
  have htrace : WordTrace (prefixWord ++ tailWord_776327) baseStart_776327 baseEnd_776327 := by
    simpa [prefixWord, tailWord_776327, baseEnd_776327] using wordTrace_append hprefix tailTrace_776327
  have hstable : (prefixWord ++ tailWord_776327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776327).length < 2 ^ (prefixWord ++ tailWord_776327).sum := by decide
  have hdescent : baseEnd_776327 < baseStart_776327 := by decide
  rcases family_descends (prefixWord ++ tailWord_776327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776389 : List Nat := [1, 3, 1, 1, 1, 1, 5, 4, 4]
def baseStart_776389 : Nat := 118140960795 + 776389 * 2 ^ 59
def prefixEnd_776389 : Nat := 4983230072969 + 3 ^ 40 * 776389 * 2
def baseEnd_776389 : Nat := 177182547494963603629759

theorem tailTrace_776389 : CollatzResearch.WordTrace tailWord_776389 prefixEnd_776389 177182547494963603629759 := by
  unfold tailWord_776389
  simp only [CollatzResearch.WordTrace]
  refine ⟨28317233184282724529748221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18878155456188483019832147 28317233184282724529748221)
  ·
    refine ⟨10618962444106021698655583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28317233184282724529748221 10618962444106021698655583)
    ·
      refine ⟨15928443666159032547983375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10618962444106021698655583 15928443666159032547983375)
      ·
        refine ⟨23892665499238548821975063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15928443666159032547983375 23892665499238548821975063)
        ·
          refine ⟨35838998248857823232962595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23892665499238548821975063 35838998248857823232962595)
          ·
            refine ⟨53758497373286734849443893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35838998248857823232962595 53758497373286734849443893)
            ·
              refine ⟨5039859128745631392135365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53758497373286734849443893 5039859128745631392135365)
              ·
                refine ⟨944973586639805886025381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5039859128745631392135365 944973586639805886025381)
                ·
                  refine ⟨177182547494963603629759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 944973586639805886025381 177182547494963603629759)
                  ·
                    rfl

theorem cell21_776389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_776389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_776389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_776389 prefixEnd_776389 := by exact prefixLift 776389
  have htrace : WordTrace (prefixWord ++ tailWord_776389) baseStart_776389 baseEnd_776389 := by
    simpa [prefixWord, tailWord_776389, baseEnd_776389] using wordTrace_append hprefix tailTrace_776389
  have hstable : (prefixWord ++ tailWord_776389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776389).length < 2 ^ (prefixWord ++ tailWord_776389).sum := by decide
  have hdescent : baseEnd_776389 < baseStart_776389 := by decide
  rcases family_descends (prefixWord ++ tailWord_776389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776451 : List Nat := [1, 1, 1, 3, 2, 3, 1, 6, 3]
def baseStart_776451 : Nat := 118140960795 + 776451 * 2 ^ 59
def prefixEnd_776451 : Nat := 4983230072969 + 3 ^ 40 * 776451 * 2
def baseEnd_776451 : Nat := 177196696739665273596299

theorem tailTrace_776451 : CollatzResearch.WordTrace tailWord_776451 prefixEnd_776451 177196696739665273596299 := by
  unfold tailWord_776451
  simp only [CollatzResearch.WordTrace]
  refine ⟨28319494510058109118505207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18879663006705406079003471 28319494510058109118505207)
  ·
    refine ⟨42479241765087163677757811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28319494510058109118505207 42479241765087163677757811)
    ·
      refine ⟨63718862647630745516636717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42479241765087163677757811 63718862647630745516636717)
      ·
        refine ⟨23894573492861529568738769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63718862647630745516636717 23894573492861529568738769)
        ·
          refine ⟨17920930119646147176554077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23894573492861529568738769 17920930119646147176554077)
          ·
            refine ⟨6720348794867305191207779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17920930119646147176554077 6720348794867305191207779)
            ·
              refine ⟨10080523192300957786811669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6720348794867305191207779 10080523192300957786811669)
              ·
                refine ⟨472524524639107396256797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10080523192300957786811669 472524524639107396256797)
                ·
                  refine ⟨177196696739665273596299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 472524524639107396256797 177196696739665273596299)
                  ·
                    rfl

theorem cell21_776451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 6, 3].length) (baseStart_776451 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_776451 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_776451 prefixEnd_776451 := by exact prefixLift 776451
  have htrace : WordTrace (prefixWord ++ tailWord_776451) baseStart_776451 baseEnd_776451 := by
    simpa [prefixWord, tailWord_776451, baseEnd_776451] using wordTrace_append hprefix tailTrace_776451
  have hstable : (prefixWord ++ tailWord_776451).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776451).length < 2 ^ (prefixWord ++ tailWord_776451).sum := by decide
  have hdescent : baseEnd_776451 < baseStart_776451 := by decide
  rcases family_descends (prefixWord ++ tailWord_776451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776485 : List Nat := [1, 3, 1, 2, 5, 2, 1, 3, 3]
def baseStart_776485 : Nat := 118140960795 + 776485 * 2 ^ 59
def prefixEnd_776485 : Nat := 4983230072969 + 3 ^ 40 * 776485 * 2
def baseEnd_776485 : Nat := 177204456002888770029563

theorem tailTrace_776485 : CollatzResearch.WordTrace tailWord_776485 prefixEnd_776485 177204456002888770029563 := by
  unfold tailWord_776485
  simp only [CollatzResearch.WordTrace]
  refine ⟨28320734591934932925242909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18880489727956621950161939 28320734591934932925242909)
  ·
    refine ⟨10620275471975599846966091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28320734591934932925242909 10620275471975599846966091)
    ·
      refine ⟨15930413207963399770449137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10620275471975599846966091 15930413207963399770449137)
      ·
        refine ⟨11947809905972549827836853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15930413207963399770449137 11947809905972549827836853)
        ·
          refine ⟨1120107178684926546359705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11947809905972549827836853 1120107178684926546359705)
          ·
            refine ⟨840080384013694909769779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1120107178684926546359705 840080384013694909769779)
            ·
              refine ⟨1260120576020542364654669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 840080384013694909769779 1260120576020542364654669)
              ·
                refine ⟨472545216007703386745501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1260120576020542364654669 472545216007703386745501)
                ·
                  refine ⟨177204456002888770029563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 472545216007703386745501 177204456002888770029563)
                  ·
                    rfl

theorem cell21_776485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 3, 3].length) (baseStart_776485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_776485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_776485 prefixEnd_776485 := by exact prefixLift 776485
  have htrace : WordTrace (prefixWord ++ tailWord_776485) baseStart_776485 baseEnd_776485 := by
    simpa [prefixWord, tailWord_776485, baseEnd_776485] using wordTrace_append hprefix tailTrace_776485
  have hstable : (prefixWord ++ tailWord_776485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776485).length < 2 ^ (prefixWord ++ tailWord_776485).sum := by decide
  have hdescent : baseEnd_776485 < baseStart_776485 := by decide
  rcases family_descends (prefixWord ++ tailWord_776485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776513 : List Nat := [1, 2, 5, 2, 2, 1, 2, 6]
def baseStart_776513 : Nat := 118140960795 + 776513 * 2 ^ 59
def prefixEnd_776513 : Nat := 4983230072969 + 3 ^ 40 * 776513 * 2
def baseEnd_776513 : Nat := 59070281994788981187613

theorem tailTrace_776513 : CollatzResearch.WordTrace tailWord_776513 prefixEnd_776513 59070281994788981187613 := by
  unfold tailWord_776513
  simp only [CollatzResearch.WordTrace]
  refine ⟨28321755835833493707262193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18881170557222329138174795 28321755835833493707262193)
  ·
    refine ⟨21241316876875120280446645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28321755835833493707262193 21241316876875120280446645)
    ·
      refine ⟨1991373457207042526291873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21241316876875120280446645 1991373457207042526291873)
      ·
        refine ⟨1493530092905281894718905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1991373457207042526291873 1493530092905281894718905)
        ·
          refine ⟨1120147569678961421039179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1493530092905281894718905 1120147569678961421039179)
          ·
            refine ⟨1680221354518442131558769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1120147569678961421039179 1680221354518442131558769)
            ·
              refine ⟨1260166015888831598669077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1680221354518442131558769 1260166015888831598669077)
              ·
                refine ⟨59070281994788981187613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1260166015888831598669077 59070281994788981187613)
                ·
                  rfl

theorem cell21_776513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 6].length) (baseStart_776513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_776513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_776513 prefixEnd_776513 := by exact prefixLift 776513
  have htrace : WordTrace (prefixWord ++ tailWord_776513) baseStart_776513 baseEnd_776513 := by
    simpa [prefixWord, tailWord_776513, baseEnd_776513] using wordTrace_append hprefix tailTrace_776513
  have hstable : (prefixWord ++ tailWord_776513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776513).length < 2 ^ (prefixWord ++ tailWord_776513).sum := by decide
  have hdescent : baseEnd_776513 < baseStart_776513 := by decide
  rcases family_descends (prefixWord ++ tailWord_776513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776648 : List Nat := [2, 1, 3, 1, 3, 2, 4, 5]
def baseStart_776648 : Nat := 118140960795 + 776648 * 2 ^ 59
def prefixEnd_776648 : Nat := 4983230072969 + 3 ^ 40 * 776648 * 2
def baseEnd_776648 : Nat := 59080551607878902937521

theorem tailTrace_776648 : CollatzResearch.WordTrace tailWord_776648 prefixEnd_776648 59080551607878902937521 := by
  unfold tailWord_776648
  simp only [CollatzResearch.WordTrace]
  refine ⟨14163339845172205881713299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18884453126896274508951065 14163339845172205881713299)
  ·
    refine ⟨21245009767758308822569949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14163339845172205881713299 21245009767758308822569949)
    ·
      refine ⟨7966878662909365808463731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21245009767758308822569949 7966878662909365808463731)
      ·
        refine ⟨11950317994364048712695597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7966878662909365808463731 11950317994364048712695597)
        ·
          refine ⟨4481369247886518267260849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11950317994364048712695597 4481369247886518267260849)
          ·
            refine ⟨3361026935914888700445637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4481369247886518267260849 3361026935914888700445637)
            ·
              refine ⟨630192550484041631333557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3361026935914888700445637 630192550484041631333557)
              ·
                refine ⟨59080551607878902937521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 630192550484041631333557 59080551607878902937521)
                ·
                  rfl

theorem cell21_776648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 5].length) (baseStart_776648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_776648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_776648 prefixEnd_776648 := by exact prefixLift 776648
  have htrace : WordTrace (prefixWord ++ tailWord_776648) baseStart_776648 baseEnd_776648 := by
    simpa [prefixWord, tailWord_776648, baseEnd_776648] using wordTrace_append hprefix tailTrace_776648
  have hstable : (prefixWord ++ tailWord_776648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776648).length < 2 ^ (prefixWord ++ tailWord_776648).sum := by decide
  have hdescent : baseEnd_776648 < baseStart_776648 := by decide
  rcases family_descends (prefixWord ++ tailWord_776648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776721 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 9]
def baseStart_776721 : Nat := 118140960795 + 776721 * 2 ^ 59
def prefixEnd_776721 : Nat := 4983230072969 + 3 ^ 40 * 776721 * 2
def baseEnd_776721 : Nat := 177258314418204804095747

theorem tailTrace_776721 : CollatzResearch.WordTrace tailWord_776721 prefixEnd_776721 177258314418204804095747 := by
  unfold tailWord_776721
  simp only [CollatzResearch.WordTrace]
  refine ⟨28329342219079945230834017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18886228146053296820556011 28329342219079945230834017)
  ·
    refine ⟨21247006664309958923125513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28329342219079945230834017 21247006664309958923125513)
    ·
      refine ⟨15935254998232469192344135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21247006664309958923125513 15935254998232469192344135)
      ·
        refine ⟨23902882497348703788516203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15935254998232469192344135 23902882497348703788516203)
        ·
          refine ⟨35854323746023055682774305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23902882497348703788516203 35854323746023055682774305)
          ·
            refine ⟨26890742809517291762080729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35854323746023055682774305 26890742809517291762080729)
            ·
              refine ⟨20168057107137968821560547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26890742809517291762080729 20168057107137968821560547)
              ·
                refine ⟨30252085660706953232340821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20168057107137968821560547 30252085660706953232340821)
                ·
                  refine ⟨177258314418204804095747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30252085660706953232340821 177258314418204804095747)
                  ·
                    rfl

theorem cell21_776721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 9].length) (baseStart_776721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_776721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_776721 prefixEnd_776721 := by exact prefixLift 776721
  have htrace : WordTrace (prefixWord ++ tailWord_776721) baseStart_776721 baseEnd_776721 := by
    simpa [prefixWord, tailWord_776721, baseEnd_776721] using wordTrace_append hprefix tailTrace_776721
  have hstable : (prefixWord ++ tailWord_776721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776721).length < 2 ^ (prefixWord ++ tailWord_776721).sum := by decide
  have hdescent : baseEnd_776721 < baseStart_776721 := by decide
  rcases family_descends (prefixWord ++ tailWord_776721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776724 : List Nat := [2, 4, 3, 1, 1, 10]
def baseStart_776724 : Nat := 118140960795 + 776724 * 2 ^ 59
def prefixEnd_776724 : Nat := 4983230072969 + 3 ^ 40 * 776724 * 2
def baseEnd_776724 : Nat := 6565148113299165390583

theorem tailTrace_776724 : CollatzResearch.WordTrace tailWord_776724 prefixEnd_776724 6565148113299165390583 := by
  unfold tailWord_776724
  simp only [CollatzResearch.WordTrace]
  refine ⟨14164725819034538371596613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18886301092046051162128817 14164725819034538371596613)
  ·
    refine ⟨2655886091068975944674365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14164725819034538371596613 2655886091068975944674365)
    ·
      refine ⟨995957284150865979252887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2655886091068975944674365 995957284150865979252887)
      ·
        refine ⟨1493935926226298968879331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 995957284150865979252887 1493935926226298968879331)
        ·
          refine ⟨2240903889339448453318997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1493935926226298968879331 2240903889339448453318997)
          ·
            refine ⟨6565148113299165390583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2240903889339448453318997 6565148113299165390583)
            ·
              rfl

theorem cell21_776724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 10].length) (baseStart_776724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_776724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_776724 prefixEnd_776724 := by exact prefixLift 776724
  have htrace : WordTrace (prefixWord ++ tailWord_776724) baseStart_776724 baseEnd_776724 := by
    simpa [prefixWord, tailWord_776724, baseEnd_776724] using wordTrace_append hprefix tailTrace_776724
  have hstable : (prefixWord ++ tailWord_776724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776724).length < 2 ^ (prefixWord ++ tailWord_776724).sum := by decide
  have hdescent : baseEnd_776724 < baseStart_776724 := by decide
  rcases family_descends (prefixWord ++ tailWord_776724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776727 : List Nat := [1, 1, 3, 6, 1, 1, 2, 2, 4]
def baseStart_776727 : Nat := 118140960795 + 776727 * 2 ^ 59
def prefixEnd_776727 : Nat := 4983230072969 + 3 ^ 40 * 776727 * 2
def baseEnd_776727 : Nat := 177259683699950126995735

theorem tailTrace_776727 : CollatzResearch.WordTrace tailWord_776727 prefixEnd_776727 177259683699950126995735 := by
  unfold tailWord_776727
  simp only [CollatzResearch.WordTrace]
  refine ⟨28329561057058208255552435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18886374038038805503701623 28329561057058208255552435)
  ·
    refine ⟨42494341585587312383328653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28329561057058208255552435 42494341585587312383328653)
    ·
      refine ⟨15935378094595242143748245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42494341585587312383328653 15935378094595242143748245)
      ·
        refine ⟨746970848184151975488199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15935378094595242143748245 746970848184151975488199)
        ·
          refine ⟨1120456272276227963232299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 746970848184151975488199 1120456272276227963232299)
          ·
            refine ⟨1680684408414341944848449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1120456272276227963232299 1680684408414341944848449)
            ·
              refine ⟨1260513306310756458636337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1680684408414341944848449 1260513306310756458636337)
              ·
                refine ⟨945384979733067343977253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1260513306310756458636337 945384979733067343977253)
                ·
                  refine ⟨177259683699950126995735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 945384979733067343977253 177259683699950126995735)
                  ·
                    rfl

theorem cell21_776727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 4].length) (baseStart_776727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_776727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_776727 prefixEnd_776727 := by exact prefixLift 776727
  have htrace : WordTrace (prefixWord ++ tailWord_776727) baseStart_776727 baseEnd_776727 := by
    simpa [prefixWord, tailWord_776727, baseEnd_776727] using wordTrace_append hprefix tailTrace_776727
  have hstable : (prefixWord ++ tailWord_776727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776727).length < 2 ^ (prefixWord ++ tailWord_776727).sum := by decide
  have hdescent : baseEnd_776727 < baseStart_776727 := by decide
  rcases family_descends (prefixWord ++ tailWord_776727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776738 : List Nat := [3, 3, 1, 1, 1, 1, 1, 5, 5]
def baseStart_776738 : Nat := 118140960795 + 776738 * 2 ^ 59
def prefixEnd_776738 : Nat := 4983230072969 + 3 ^ 40 * 776738 * 2
def baseEnd_776738 : Nat := 177262194049816552312379

theorem tailTrace_776738 : CollatzResearch.WordTrace tailWord_776738 prefixEnd_776738 177262194049816552312379 := by
  unfold tailWord_776738
  simp only [CollatzResearch.WordTrace]
  refine ⟨7082490565004589283550717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18886641506678904756135245 7082490565004589283550717)
  ·
    refine ⟨2655933961876720981331519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7082490565004589283550717 2655933961876720981331519)
    ·
      refine ⟨3983900942815081471997279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2655933961876720981331519 3983900942815081471997279)
      ·
        refine ⟨5975851414222622207995919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3983900942815081471997279 5975851414222622207995919)
        ·
          refine ⟨8963777121333933311993879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5975851414222622207995919 8963777121333933311993879)
          ·
            refine ⟨13445665682000899967990819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8963777121333933311993879 13445665682000899967990819)
            ·
              refine ⟨20168498523001349951986229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13445665682000899967990819 20168498523001349951986229)
              ·
                refine ⟨1890796736531376557998709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20168498523001349951986229 1890796736531376557998709)
                ·
                  refine ⟨177262194049816552312379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1890796736531376557998709 177262194049816552312379)
                  ·
                    rfl

theorem cell21_776738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_776738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_776738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_776738 prefixEnd_776738 := by exact prefixLift 776738
  have htrace : WordTrace (prefixWord ++ tailWord_776738) baseStart_776738 baseEnd_776738 := by
    simpa [prefixWord, tailWord_776738, baseEnd_776738] using wordTrace_append hprefix tailTrace_776738
  have hstable : (prefixWord ++ tailWord_776738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776738).length < 2 ^ (prefixWord ++ tailWord_776738).sum := by decide
  have hdescent : baseEnd_776738 < baseStart_776738 := by decide
  rcases family_descends (prefixWord ++ tailWord_776738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776828 : List Nat := [2, 2, 2, 1, 1, 2, 3, 2, 6]
def baseStart_776828 : Nat := 118140960795 + 776828 * 2 ^ 59
def prefixEnd_776828 : Nat := 4983230072969 + 3 ^ 40 * 776828 * 2
def baseEnd_776828 : Nat := 177282733275996395812195

theorem tailTrace_776828 : CollatzResearch.WordTrace tailWord_776828 prefixEnd_776828 177282733275996395812195 := by
  unfold tailWord_776828
  simp only [CollatzResearch.WordTrace]
  refine ⟨14166622414846151252489569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18888829886461535003319425 14166622414846151252489569)
  ·
    refine ⟨10624966811134613439367177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14166622414846151252489569 10624966811134613439367177)
    ·
      refine ⟨7968725108350960079525383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10624966811134613439367177 7968725108350960079525383)
      ·
        refine ⟨11953087662526440119288075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7968725108350960079525383 11953087662526440119288075)
        ·
          refine ⟨17929631493789660178932113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11953087662526440119288075 17929631493789660178932113)
          ·
            refine ⟨13447223620342245134199085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17929631493789660178932113 13447223620342245134199085)
            ·
              refine ⟨5042708857628341925324657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13447223620342245134199085 5042708857628341925324657)
              ·
                refine ⟨3782031643221256443993493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5042708857628341925324657 3782031643221256443993493)
                ·
                  refine ⟨177282733275996395812195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3782031643221256443993493 177282733275996395812195)
                  ·
                    rfl

theorem cell21_776828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_776828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_776828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_776828 prefixEnd_776828 := by exact prefixLift 776828
  have htrace : WordTrace (prefixWord ++ tailWord_776828) baseStart_776828 baseEnd_776828 := by
    simpa [prefixWord, tailWord_776828, baseEnd_776828] using wordTrace_append hprefix tailTrace_776828
  have hstable : (prefixWord ++ tailWord_776828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776828).length < 2 ^ (prefixWord ++ tailWord_776828).sum := by decide
  have hdescent : baseEnd_776828 < baseStart_776828 := by decide
  rcases family_descends (prefixWord ++ tailWord_776828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776862 : List Nat := [4, 3, 1, 1, 1, 1, 3, 3, 4]
def baseStart_776862 : Nat := 118140960795 + 776862 * 2 ^ 59
def prefixEnd_776862 : Nat := 4983230072969 + 3 ^ 40 * 776862 * 2
def baseEnd_776862 : Nat := 177290492539219892245459

theorem tailTrace_776862 : CollatzResearch.WordTrace tailWord_776862 prefixEnd_776862 177290492539219892245459 := by
  unfold tailWord_776862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3541810613946140788964605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18889656607712750874477893 3541810613946140788964605)
  ·
    refine ⟨1328178980229802795861727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3541810613946140788964605 1328178980229802795861727)
    ·
      refine ⟨1992268470344704193792591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1328178980229802795861727 1992268470344704193792591)
      ·
        refine ⟨2988402705517056290688887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1992268470344704193792591 2988402705517056290688887)
        ·
          refine ⟨4482604058275584436033331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2988402705517056290688887 4482604058275584436033331)
          ·
            refine ⟨6723906087413376654049997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4482604058275584436033331 6723906087413376654049997)
            ·
              refine ⟨2521464782780016245268749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6723906087413376654049997 2521464782780016245268749)
              ·
                refine ⟨945549293542506091975781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2521464782780016245268749 945549293542506091975781)
                ·
                  refine ⟨177290492539219892245459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 945549293542506091975781 177290492539219892245459)
                  ·
                    rfl

theorem cell21_776862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_776862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_776862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_776862 prefixEnd_776862 := by exact prefixLift 776862
  have htrace : WordTrace (prefixWord ++ tailWord_776862) baseStart_776862 baseEnd_776862 := by
    simpa [prefixWord, tailWord_776862, baseEnd_776862] using wordTrace_append hprefix tailTrace_776862
  have hstable : (prefixWord ++ tailWord_776862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776862).length < 2 ^ (prefixWord ++ tailWord_776862).sum := by decide
  have hdescent : baseEnd_776862 < baseStart_776862 := by decide
  rcases family_descends (prefixWord ++ tailWord_776862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777011 : List Nat := [1, 1, 1, 2, 6, 3, 7]
def baseStart_777011 : Nat := 118140960795 + 777011 * 2 ^ 59
def prefixEnd_777011 : Nat := 4983230072969 + 3 ^ 40 * 777011 * 2
def baseEnd_777011 : Nat := 19702721818803193806869

theorem tailTrace_777011 : CollatzResearch.WordTrace tailWord_777011 prefixEnd_777011 19702721818803193806869 := by
  unfold tailWord_777011
  simp only [CollatzResearch.WordTrace]
  refine ⟨28339919388029324758890887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18893279592019549839260591 28339919388029324758890887)
  ·
    refine ⟨42509879082043987138336331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28339919388029324758890887 42509879082043987138336331)
    ·
      refine ⟨63764818623065980707504497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42509879082043987138336331 63764818623065980707504497)
      ·
        refine ⟨47823613967299485530628373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63764818623065980707504497 47823613967299485530628373)
        ·
          refine ⟨2241731904717163384248205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47823613967299485530628373 2241731904717163384248205)
          ·
            refine ⟨840649464268936269093077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2241731904717163384248205 840649464268936269093077)
            ·
              refine ⟨19702721818803193806869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 840649464268936269093077 19702721818803193806869)
              ·
                rfl

theorem cell21_777011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 7].length) (baseStart_777011 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_777011 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_777011 prefixEnd_777011 := by exact prefixLift 777011
  have htrace : WordTrace (prefixWord ++ tailWord_777011) baseStart_777011 baseEnd_777011 := by
    simpa [prefixWord, tailWord_777011, baseEnd_777011] using wordTrace_append hprefix tailTrace_777011
  have hstable : (prefixWord ++ tailWord_777011).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777011).length < 2 ^ (prefixWord ++ tailWord_777011).sum := by decide
  have hdescent : baseEnd_777011 < baseStart_777011 := by decide
  rcases family_descends (prefixWord ++ tailWord_777011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777073 : List Nat := [1, 2, 2, 2, 1, 5, 2, 2, 4]
def baseStart_777073 : Nat := 118140960795 + 777073 * 2 ^ 59
def prefixEnd_777073 : Nat := 4983230072969 + 3 ^ 40 * 777073 * 2
def baseEnd_777073 : Nat := 177338645613930414228361

theorem tailTrace_777073 : CollatzResearch.WordTrace tailWord_777073 prefixEnd_777073 177338645613930414228361 := by
  unfold tailWord_777073
  simp only [CollatzResearch.WordTrace]
  refine ⟨28342180713804709347647873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18894787142536472898431915 28342180713804709347647873)
  ·
    refine ⟨21256635535353532010735905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28342180713804709347647873 21256635535353532010735905)
    ·
      refine ⟨15942476651515149008051929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21256635535353532010735905 15942476651515149008051929)
      ·
        refine ⟨11956857488636361756038947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15942476651515149008051929 11956857488636361756038947)
        ·
          refine ⟨17935286232954542634058421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11956857488636361756038947 17935286232954542634058421)
          ·
            refine ⟨1681433084339488371942977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17935286232954542634058421 1681433084339488371942977)
            ·
              refine ⟨1261074813254616278957233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1681433084339488371942977 1261074813254616278957233)
              ·
                refine ⟨945806109940962209217925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1261074813254616278957233 945806109940962209217925)
                ·
                  refine ⟨177338645613930414228361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 945806109940962209217925 177338645613930414228361)
                  ·
                    rfl

theorem cell21_777073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 4].length) (baseStart_777073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_777073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_777073 prefixEnd_777073 := by exact prefixLift 777073
  have htrace : WordTrace (prefixWord ++ tailWord_777073) baseStart_777073 baseEnd_777073 := by
    simpa [prefixWord, tailWord_777073, baseEnd_777073] using wordTrace_append hprefix tailTrace_777073
  have hstable : (prefixWord ++ tailWord_777073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777073).length < 2 ^ (prefixWord ++ tailWord_777073).sum := by decide
  have hdescent : baseEnd_777073 < baseStart_777073 := by decide
  rcases family_descends (prefixWord ++ tailWord_777073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777110 : List Nat := [5, 3, 1, 1, 1, 2, 2, 3, 3]
def baseStart_777110 : Nat := 118140960795 + 777110 * 2 ^ 59
def prefixEnd_777110 : Nat := 4983230072969 + 3 ^ 40 * 777110 * 2
def baseEnd_777110 : Nat := 177347089518026572111619

theorem tailTrace_777110 : CollatzResearch.WordTrace tailWord_777110 prefixEnd_777110 177347089518026572111619 := by
  unfold tailWord_777110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1771470638416916541671549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18895686809780443111163189 1771470638416916541671549)
  ·
    refine ⟨664301489406343703126831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1771470638416916541671549 664301489406343703126831)
    ·
      refine ⟨996452234109515554690247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 664301489406343703126831 996452234109515554690247)
      ·
        refine ⟨1494678351164273332035371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 996452234109515554690247 1494678351164273332035371)
        ·
          refine ⟨2242017526746409998053057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1494678351164273332035371 2242017526746409998053057)
          ·
            refine ⟨1681513145059807498539793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2242017526746409998053057 1681513145059807498539793)
            ·
              refine ⟨1261134858794855623904845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1681513145059807498539793 1261134858794855623904845)
              ·
                refine ⟨472925572048070858964317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1261134858794855623904845 472925572048070858964317)
                ·
                  refine ⟨177347089518026572111619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 472925572048070858964317 177347089518026572111619)
                  ·
                    rfl

theorem cell21_777110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_777110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_777110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_777110 prefixEnd_777110 := by exact prefixLift 777110
  have htrace : WordTrace (prefixWord ++ tailWord_777110) baseStart_777110 baseEnd_777110 := by
    simpa [prefixWord, tailWord_777110, baseEnd_777110] using wordTrace_append hprefix tailTrace_777110
  have hstable : (prefixWord ++ tailWord_777110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777110).length < 2 ^ (prefixWord ++ tailWord_777110).sum := by decide
  have hdescent : baseEnd_777110 < baseStart_777110 := by decide
  rcases family_descends (prefixWord ++ tailWord_777110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777146 : List Nat := [3, 1, 1, 1, 2, 1, 4, 8]
def baseStart_777146 : Nat := 118140960795 + 777146 * 2 ^ 59
def prefixEnd_777146 : Nat := 4983230072969 + 3 ^ 40 * 777146 * 2
def baseEnd_777146 : Nat := 59118435069499503170515

theorem tailTrace_777146 : CollatzResearch.WordTrace tailWord_777146 prefixEnd_777146 59118435069499503170515 := by
  unfold tailWord_777146
  simp only [CollatzResearch.WordTrace]
  refine ⟨7086210810635060703763823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18896562161693495210036861 7086210810635060703763823)
  ·
    refine ⟨10629316215952591055645735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7086210810635060703763823 10629316215952591055645735)
    ·
      refine ⟨15943974323928886583468603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10629316215952591055645735 15943974323928886583468603)
      ·
        refine ⟨23915961485893329875202905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15943974323928886583468603 23915961485893329875202905)
        ·
          refine ⟨17936971114419997406402179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23915961485893329875202905 17936971114419997406402179)
          ·
            refine ⟨26905456671629996109603269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17936971114419997406402179 26905456671629996109603269)
            ·
              refine ⟨5044773125930624270550613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26905456671629996109603269 5044773125930624270550613)
              ·
                refine ⟨59118435069499503170515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5044773125930624270550613 59118435069499503170515)
                ·
                  rfl

theorem cell21_777146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 8].length) (baseStart_777146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_777146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_777146 prefixEnd_777146 := by exact prefixLift 777146
  have htrace : WordTrace (prefixWord ++ tailWord_777146) baseStart_777146 baseEnd_777146 := by
    simpa [prefixWord, tailWord_777146, baseEnd_777146] using wordTrace_append hprefix tailTrace_777146
  have hstable : (prefixWord ++ tailWord_777146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777146).length < 2 ^ (prefixWord ++ tailWord_777146).sum := by decide
  have hdescent : baseEnd_777146 < baseStart_777146 := by decide
  rcases family_descends (prefixWord ++ tailWord_777146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777163 : List Nat := [1, 1, 1, 1, 3, 5, 4, 5]
def baseStart_777163 : Nat := 118140960795 + 777163 * 2 ^ 59
def prefixEnd_777163 : Nat := 4983230072969 + 3 ^ 40 * 777163 * 2
def baseEnd_777163 : Nat := 59119728280036752576059

theorem tailTrace_777163 : CollatzResearch.WordTrace tailWord_777163 prefixEnd_777163 59119728280036752576059 := by
  unfold tailWord_777163
  simp only [CollatzResearch.WordTrace]
  refine ⟨28345463283478654718424143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18896975522319103145616095 28345463283478654718424143)
  ·
    refine ⟨42518194925217982077636215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28345463283478654718424143 42518194925217982077636215)
    ·
      refine ⟨63777292387826973116454323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42518194925217982077636215 63777292387826973116454323)
      ·
        refine ⟨95665938581740459674681485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63777292387826973116454323 95665938581740459674681485)
        ·
          refine ⟨35874726968152672378005557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95665938581740459674681485 35874726968152672378005557)
          ·
            refine ⟨3363255653264313035438021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35874726968152672378005557 3363255653264313035438021)
            ·
              refine ⟨630610434987058694144629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3363255653264313035438021 630610434987058694144629)
              ·
                refine ⟨59119728280036752576059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 630610434987058694144629 59119728280036752576059)
                ·
                  rfl

theorem cell21_777163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 5].length) (baseStart_777163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_777163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_777163 prefixEnd_777163 := by exact prefixLift 777163
  have htrace : WordTrace (prefixWord ++ tailWord_777163) baseStart_777163 baseEnd_777163 := by
    simpa [prefixWord, tailWord_777163, baseEnd_777163] using wordTrace_append hprefix tailTrace_777163
  have hstable : (prefixWord ++ tailWord_777163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777163).length < 2 ^ (prefixWord ++ tailWord_777163).sum := by decide
  have hdescent : baseEnd_777163 < baseStart_777163 := by decide
  rcases family_descends (prefixWord ++ tailWord_777163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777194 : List Nat := [3, 1, 3, 1, 2, 2, 3, 1, 5]
def baseStart_777194 : Nat := 118140960795 + 777194 * 2 ^ 59
def prefixEnd_777194 : Nat := 4983230072969 + 3 ^ 40 * 777194 * 2
def baseEnd_777194 : Nat := 177366259462461092711447

theorem tailTrace_777194 : CollatzResearch.WordTrace tailWord_777194 prefixEnd_777194 177366259462461092711447 := by
  unfold tailWord_777194
  simp only [CollatzResearch.WordTrace]
  refine ⟨7086648486591586753200659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18897729297577564675201757 7086648486591586753200659)
  ·
    refine ⟨10629972729887380129800989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7086648486591586753200659 10629972729887380129800989)
    ·
      refine ⟨3986239773707767548675371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10629972729887380129800989 3986239773707767548675371)
      ·
        refine ⟨5979359660561651323013057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3986239773707767548675371 5979359660561651323013057)
        ·
          refine ⟨4484519745421238492259793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5979359660561651323013057 4484519745421238492259793)
          ·
            refine ⟨3363389809065928869194845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4484519745421238492259793 3363389809065928869194845)
            ·
              refine ⟨1261271178399723325948067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3363389809065928869194845 1261271178399723325948067)
              ·
                refine ⟨1891906767599584988922101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1261271178399723325948067 1891906767599584988922101)
                ·
                  refine ⟨177366259462461092711447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1891906767599584988922101 177366259462461092711447)
                  ·
                    rfl

theorem cell21_777194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_777194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_777194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_777194 prefixEnd_777194 := by exact prefixLift 777194
  have htrace : WordTrace (prefixWord ++ tailWord_777194) baseStart_777194 baseEnd_777194 := by
    simpa [prefixWord, tailWord_777194, baseEnd_777194] using wordTrace_append hprefix tailTrace_777194
  have hstable : (prefixWord ++ tailWord_777194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777194).length < 2 ^ (prefixWord ++ tailWord_777194).sum := by decide
  have hdescent : baseEnd_777194 < baseStart_777194 := by decide
  rcases family_descends (prefixWord ++ tailWord_777194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777245 : List Nat := [1, 4, 2, 2, 3, 2, 2, 2, 3]
def baseStart_777245 : Nat := 118140960795 + 777245 * 2 ^ 59
def prefixEnd_777245 : Nat := 4983230072969 + 3 ^ 40 * 777245 * 2
def baseEnd_777245 : Nat := 177377898357296337361343

theorem tailTrace_777245 : CollatzResearch.WordTrace tailWord_777245 prefixEnd_777245 177377898357296337361343 := by
  unfold tailWord_777245
  simp only [CollatzResearch.WordTrace]
  refine ⟨28348454069181582722909189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18898969379454388481939459 28348454069181582722909189)
  ·
    refine ⟨5315335137971546760545473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28348454069181582722909189 5315335137971546760545473)
    ·
      refine ⟨3986501353478660070409105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5315335137971546760545473 3986501353478660070409105)
      ·
        refine ⟨2989876015108995052806829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3986501353478660070409105 2989876015108995052806829)
        ·
          refine ⟨1121203505665873144802561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2989876015108995052806829 1121203505665873144802561)
          ·
            refine ⟨840902629249404858601921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1121203505665873144802561 840902629249404858601921)
            ·
              refine ⟨630676971937053643951441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 840902629249404858601921 630676971937053643951441)
              ·
                refine ⟨473007728952790232963581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 630676971937053643951441 473007728952790232963581)
                ·
                  refine ⟨177377898357296337361343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 473007728952790232963581 177377898357296337361343)
                  ·
                    rfl

theorem cell21_777245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_777245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_777245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_777245 prefixEnd_777245 := by exact prefixLift 777245
  have htrace : WordTrace (prefixWord ++ tailWord_777245) baseStart_777245 baseEnd_777245 := by
    simpa [prefixWord, tailWord_777245, baseEnd_777245] using wordTrace_append hprefix tailTrace_777245
  have hstable : (prefixWord ++ tailWord_777245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777245).length < 2 ^ (prefixWord ++ tailWord_777245).sum := by decide
  have hdescent : baseEnd_777245 < baseStart_777245 := by decide
  rcases family_descends (prefixWord ++ tailWord_777245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777253 : List Nat := [1, 3, 1, 2, 2, 2, 2, 3, 5]
def baseStart_777253 : Nat := 118140960795 + 777253 * 2 ^ 59
def prefixEnd_777253 : Nat := 4983230072969 + 3 ^ 40 * 777253 * 2
def baseEnd_777253 : Nat := 177379724066290101227993

theorem tailTrace_777253 : CollatzResearch.WordTrace tailWord_777253 prefixEnd_777253 177379724066290101227993 := by
  unfold tailWord_777253
  simp only [CollatzResearch.WordTrace]
  refine ⟨28348745853152600089200413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18899163902101733392800275 28348745853152600089200413)
  ·
    refine ⟨10630779694932225033450155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28348745853152600089200413 10630779694932225033450155)
    ·
      refine ⟨15946169542398337550175233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10630779694932225033450155 15946169542398337550175233)
      ·
        refine ⟨11959627156798753162631425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15946169542398337550175233 11959627156798753162631425)
        ·
          refine ⟨8969720367599064871973569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11959627156798753162631425 8969720367599064871973569)
          ·
            refine ⟨6727290275699298653980177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8969720367599064871973569 6727290275699298653980177)
            ·
              refine ⟨5045467706774473990485133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6727290275699298653980177 5045467706774473990485133)
              ·
                refine ⟨1892050390040427746431925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5045467706774473990485133 1892050390040427746431925)
                ·
                  refine ⟨177379724066290101227993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1892050390040427746431925 177379724066290101227993)
                  ·
                    rfl

theorem cell21_777253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_777253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_777253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_777253 prefixEnd_777253 := by exact prefixLift 777253
  have htrace : WordTrace (prefixWord ++ tailWord_777253) baseStart_777253 baseEnd_777253 := by
    simpa [prefixWord, tailWord_777253, baseEnd_777253] using wordTrace_append hprefix tailTrace_777253
  have hstable : (prefixWord ++ tailWord_777253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777253).length < 2 ^ (prefixWord ++ tailWord_777253).sum := by decide
  have hdescent : baseEnd_777253 < baseStart_777253 := by decide
  rcases family_descends (prefixWord ++ tailWord_777253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777267 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 8]
def baseStart_777267 : Nat := 118140960795 + 777267 * 2 ^ 59
def prefixEnd_777267 : Nat := 4983230072969 + 3 ^ 40 * 777267 * 2
def baseEnd_777267 : Nat := 177382919057029187994631

theorem tailTrace_777267 : CollatzResearch.WordTrace tailWord_777267 prefixEnd_777267 177382919057029187994631 := by
  unfold tailWord_777267
  simp only [CollatzResearch.WordTrace]
  refine ⟨28349256475101880480210055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18899504316734586986806703 28349256475101880480210055)
  ·
    refine ⟨42523884712652820720315083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28349256475101880480210055 42523884712652820720315083)
    ·
      refine ⟨63785827068979231080472625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42523884712652820720315083 63785827068979231080472625)
      ·
        refine ⟨47839370301734423310354469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63785827068979231080472625 47839370301734423310354469)
        ·
          refine ⟨8969881931575204370691463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47839370301734423310354469 8969881931575204370691463)
          ·
            refine ⟨13454822897362806556037195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8969881931575204370691463 13454822897362806556037195)
            ·
              refine ⟨20182234346044209834055793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13454822897362806556037195 20182234346044209834055793)
              ·
                refine ⟨15136675759533157375541845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20182234346044209834055793 15136675759533157375541845)
                ·
                  refine ⟨177382919057029187994631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15136675759533157375541845 177382919057029187994631)
                  ·
                    rfl

theorem cell21_777267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 8].length) (baseStart_777267 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_777267 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_777267 prefixEnd_777267 := by exact prefixLift 777267
  have htrace : WordTrace (prefixWord ++ tailWord_777267) baseStart_777267 baseEnd_777267 := by
    simpa [prefixWord, tailWord_777267, baseEnd_777267] using wordTrace_append hprefix tailTrace_777267
  have hstable : (prefixWord ++ tailWord_777267).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777267).length < 2 ^ (prefixWord ++ tailWord_777267).sum := by decide
  have hdescent : baseEnd_777267 < baseStart_777267 := by decide
  rcases family_descends (prefixWord ++ tailWord_777267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777270 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 7]
def baseStart_777270 : Nat := 118140960795 + 777270 * 2 ^ 59
def prefixEnd_777270 : Nat := 4983230072969 + 3 ^ 40 * 777270 * 2
def baseEnd_777270 : Nat := 177383603697901849444625

theorem tailTrace_777270 : CollatzResearch.WordTrace tailWord_777270 prefixEnd_777270 177383603697901849444625 := by
  unfold tailWord_777270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1771835368380688249535579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18899577262727341328379509 1771835368380688249535579)
  ·
    refine ⟨2657753052571032374303369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1771835368380688249535579 2657753052571032374303369)
    ·
      refine ⟨1993314789428274280727527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2657753052571032374303369 1993314789428274280727527)
      ·
        refine ⟨2989972184142411421091291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1993314789428274280727527 2989972184142411421091291)
        ·
          refine ⟨4484958276213617131636937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2989972184142411421091291 4484958276213617131636937)
          ·
            refine ⟨3363718707160212848727703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4484958276213617131636937 3363718707160212848727703)
            ·
              refine ⟨5045578060740319273091555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3363718707160212848727703 5045578060740319273091555)
              ·
                refine ⟨7568367091110478909637333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5045578060740319273091555 7568367091110478909637333)
                ·
                  refine ⟨177383603697901849444625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7568367091110478909637333 177383603697901849444625)
                  ·
                    rfl

theorem cell21_777270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_777270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_777270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_777270 prefixEnd_777270 := by exact prefixLift 777270
  have htrace : WordTrace (prefixWord ++ tailWord_777270) baseStart_777270 baseEnd_777270 := by
    simpa [prefixWord, tailWord_777270, baseEnd_777270] using wordTrace_append hprefix tailTrace_777270
  have hstable : (prefixWord ++ tailWord_777270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777270).length < 2 ^ (prefixWord ++ tailWord_777270).sum := by decide
  have hdescent : baseEnd_777270 < baseStart_777270 := by decide
  rcases family_descends (prefixWord ++ tailWord_777270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777287 : List Nat := [1, 1, 4, 1, 3, 3, 2, 3, 3]
def baseStart_777287 : Nat := 118140960795 + 777287 * 2 ^ 59
def prefixEnd_777287 : Nat := 4983230072969 + 3 ^ 40 * 777287 * 2
def baseEnd_777287 : Nat := 177387483329513597661257

theorem tailTrace_777287 : CollatzResearch.WordTrace tailWord_777287 prefixEnd_777287 177387483329513597661257 := by
  unfold tailWord_777287
  simp only [CollatzResearch.WordTrace]
  refine ⟨28349985935029423895938115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18899990623352949263958743 28349985935029423895938115)
  ·
    refine ⟨42524978902544135843907173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28349985935029423895938115 42524978902544135843907173)
    ·
      refine ⟨7973433544227025470732595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42524978902544135843907173 7973433544227025470732595)
      ·
        refine ⟨11960150316340538206098893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7973433544227025470732595 11960150316340538206098893)
        ·
          refine ⟨4485056368627701827287085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11960150316340538206098893 4485056368627701827287085)
          ·
            refine ⟨1681896138235388185232657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4485056368627701827287085 1681896138235388185232657)
            ·
              refine ⟨1261422103676541138924493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1681896138235388185232657 1261422103676541138924493)
              ·
                refine ⟨473033288878702927096685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1261422103676541138924493 473033288878702927096685)
                ·
                  refine ⟨177387483329513597661257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 473033288878702927096685 177387483329513597661257)
                  ·
                    rfl

theorem cell21_777287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 3, 3].length) (baseStart_777287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_777287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_777287 prefixEnd_777287 := by exact prefixLift 777287
  have htrace : WordTrace (prefixWord ++ tailWord_777287) baseStart_777287 baseEnd_777287 := by
    simpa [prefixWord, tailWord_777287, baseEnd_777287] using wordTrace_append hprefix tailTrace_777287
  have hstable : (prefixWord ++ tailWord_777287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777287).length < 2 ^ (prefixWord ++ tailWord_777287).sum := by decide
  have hdescent : baseEnd_777287 < baseStart_777287 := by decide
  rcases family_descends (prefixWord ++ tailWord_777287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777414 : List Nat := [6, 1, 2, 2, 1, 1, 1, 4, 3]
def baseStart_777414 : Nat := 118140960795 + 777414 * 2 ^ 59
def prefixEnd_777414 : Nat := 4983230072969 + 3 ^ 40 * 777414 * 2
def baseEnd_777414 : Nat := 177416466459789599044331

theorem tailTrace_777414 : CollatzResearch.WordTrace tailWord_777414 prefixEnd_777414 177416466459789599044331 := by
  unfold tailWord_777414
  simp only [CollatzResearch.WordTrace]
  refine ⟨886081812674041393306603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18903078670379549723874197 886081812674041393306603)
  ·
    refine ⟨1329122719011062089959905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 886081812674041393306603 1329122719011062089959905)
    ·
      refine ⟨996842039258296567469929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1329122719011062089959905 996842039258296567469929)
      ·
        refine ⟨747631529443722425602447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 996842039258296567469929 747631529443722425602447)
        ·
          refine ⟨1121447294165583638403671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 747631529443722425602447 1121447294165583638403671)
          ·
            refine ⟨1682170941248375457605507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1121447294165583638403671 1682170941248375457605507)
            ·
              refine ⟨2523256411872563186408261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1682170941248375457605507 2523256411872563186408261)
              ·
                refine ⟨473110577226105597451549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2523256411872563186408261 473110577226105597451549)
                ·
                  refine ⟨177416466459789599044331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 473110577226105597451549 177416466459789599044331)
                  ·
                    rfl

theorem cell21_777414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_777414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_777414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_777414 prefixEnd_777414 := by exact prefixLift 777414
  have htrace : WordTrace (prefixWord ++ tailWord_777414) baseStart_777414 baseEnd_777414 := by
    simpa [prefixWord, tailWord_777414, baseEnd_777414] using wordTrace_append hprefix tailTrace_777414
  have hstable : (prefixWord ++ tailWord_777414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777414).length < 2 ^ (prefixWord ++ tailWord_777414).sum := by decide
  have hdescent : baseEnd_777414 < baseStart_777414 := by decide
  rcases family_descends (prefixWord ++ tailWord_777414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777470 : List Nat := [4, 2, 2, 1, 1, 4, 1, 2, 4]
def baseStart_777470 : Nat := 118140960795 + 777470 * 2 ^ 59
def prefixEnd_777470 : Nat := 4983230072969 + 3 ^ 40 * 777470 * 2
def baseEnd_777470 : Nat := 177429246422745946110883

theorem tailTrace_777470 : CollatzResearch.WordTrace tailWord_777470 prefixEnd_777470 177429246422745946110883 := by
  unfold tailWord_777470
  simp only [CollatzResearch.WordTrace]
  refine ⟨3544582561670805768731233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18904440328910964099899909 3544582561670805768731233)
  ·
    refine ⟨2658436921253104326548425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3544582561670805768731233 2658436921253104326548425)
    ·
      refine ⟨1993827690939828244911319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2658436921253104326548425 1993827690939828244911319)
      ·
        refine ⟨2990741536409742367366979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1993827690939828244911319 2990741536409742367366979)
        ·
          refine ⟨4486112304614613551050469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2990741536409742367366979 4486112304614613551050469)
          ·
            refine ⟨841146057115240040821963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4486112304614613551050469 841146057115240040821963)
            ·
              refine ⟨1261719085672860061232945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 841146057115240040821963 1261719085672860061232945)
              ·
                refine ⟨946289314254645045924709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1261719085672860061232945 946289314254645045924709)
                ·
                  refine ⟨177429246422745946110883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 946289314254645045924709 177429246422745946110883)
                  ·
                    rfl

theorem cell21_777470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_777470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_777470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_777470 prefixEnd_777470 := by exact prefixLift 777470
  have htrace : WordTrace (prefixWord ++ tailWord_777470) baseStart_777470 baseEnd_777470 := by
    simpa [prefixWord, tailWord_777470, baseEnd_777470] using wordTrace_append hprefix tailTrace_777470
  have hstable : (prefixWord ++ tailWord_777470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777470).length < 2 ^ (prefixWord ++ tailWord_777470).sum := by decide
  have hdescent : baseEnd_777470 < baseStart_777470 := by decide
  rcases family_descends (prefixWord ++ tailWord_777470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777481 : List Nat := [1, 2, 1, 1, 3, 3, 4, 1, 5]
def baseStart_777481 : Nat := 118140960795 + 777481 * 2 ^ 59
def prefixEnd_777481 : Nat := 4983230072969 + 3 ^ 40 * 777481 * 2
def baseEnd_777481 : Nat := 177431756772612371427527

theorem tailTrace_777481 : CollatzResearch.WordTrace tailWord_777481 prefixEnd_777481 177431756772612371427527 := by
  unfold tailWord_777481
  simp only [CollatzResearch.WordTrace]
  refine ⟨28357061696326595028500297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18904707797551063352333531 28357061696326595028500297)
  ·
    refine ⟨21267796272244946271375223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28357061696326595028500297 21267796272244946271375223)
    ·
      refine ⟨31901694408367419407062835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21267796272244946271375223 31901694408367419407062835)
      ·
        refine ⟨47852541612551129110594253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31901694408367419407062835 47852541612551129110594253)
        ·
          refine ⟨17944703104706673416472845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47852541612551129110594253 17944703104706673416472845)
          ·
            refine ⟨6729263664265002531177317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17944703104706673416472845 6729263664265002531177317)
            ·
              refine ⟨1261736937049687974595747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6729263664265002531177317 1261736937049687974595747)
              ·
                refine ⟨1892605405574531961893621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1261736937049687974595747 1892605405574531961893621)
                ·
                  refine ⟨177431756772612371427527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1892605405574531961893621 177431756772612371427527)
                  ·
                    rfl

theorem cell21_777481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 5].length) (baseStart_777481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_777481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_777481 prefixEnd_777481 := by exact prefixLift 777481
  have htrace : WordTrace (prefixWord ++ tailWord_777481) baseStart_777481 baseEnd_777481 := by
    simpa [prefixWord, tailWord_777481, baseEnd_777481] using wordTrace_append hprefix tailTrace_777481
  have hstable : (prefixWord ++ tailWord_777481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777481).length < 2 ^ (prefixWord ++ tailWord_777481).sum := by decide
  have hdescent : baseEnd_777481 < baseStart_777481 := by decide
  rcases family_descends (prefixWord ++ tailWord_777481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777512 : List Nat := [2, 1, 5, 1, 2, 1, 1, 2, 6]
def baseStart_777512 : Nat := 118140960795 + 777512 * 2 ^ 59
def prefixEnd_777512 : Nat := 4983230072969 + 3 ^ 40 * 777512 * 2
def baseEnd_777512 : Nat := 177438831394963206410797

theorem tailTrace_777512 : CollatzResearch.WordTrace tailWord_777512 prefixEnd_777512 177438831394963206410797 := by
  unfold tailWord_777512
  simp only [CollatzResearch.WordTrace]
  refine ⟨14179096179607143661439395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18905461572809524881919193 14179096179607143661439395)
  ·
    refine ⟨21268644269410715492159093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14179096179607143661439395 21268644269410715492159093)
    ·
      refine ⟨1993935400257254577389915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21268644269410715492159093 1993935400257254577389915)
      ·
        refine ⟨2990903100385881866084873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1993935400257254577389915 2990903100385881866084873)
        ·
          refine ⟨2243177325289411399563655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2990903100385881866084873 2243177325289411399563655)
          ·
            refine ⟨3364765987934117099345483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2243177325289411399563655 3364765987934117099345483)
            ·
              refine ⟨5047148981901175649018225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3364765987934117099345483 5047148981901175649018225)
              ·
                refine ⟨3785361736425881736763669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5047148981901175649018225 3785361736425881736763669)
                ·
                  refine ⟨177438831394963206410797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3785361736425881736763669 177438831394963206410797)
                  ·
                    rfl

theorem cell21_777512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 6].length) (baseStart_777512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_777512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_777512 prefixEnd_777512 := by exact prefixLift 777512
  have htrace : WordTrace (prefixWord ++ tailWord_777512) baseStart_777512 baseEnd_777512 := by
    simpa [prefixWord, tailWord_777512, baseEnd_777512] using wordTrace_append hprefix tailTrace_777512
  have hstable : (prefixWord ++ tailWord_777512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777512).length < 2 ^ (prefixWord ++ tailWord_777512).sum := by decide
  have hdescent : baseEnd_777512 < baseStart_777512 := by decide
  rcases family_descends (prefixWord ++ tailWord_777512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777684 : List Nat := [2, 4, 1, 2, 3, 2, 1, 3, 3]
def baseStart_777684 : Nat := 118140960795 + 777684 * 2 ^ 59
def prefixEnd_777684 : Nat := 4983230072969 + 3 ^ 40 * 777684 * 2
def baseEnd_777684 : Nat := 177478084138329129543779

theorem tailTrace_777684 : CollatzResearch.WordTrace tailWord_777684 prefixEnd_777684 177478084138329129543779 := by
  unfold tailWord_777684
  simp only [CollatzResearch.WordTrace]
  refine ⟨14182232857295580349070053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18909643809727440465426737 14182232857295580349070053)
  ·
    refine ⟨2659168660742921315450635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14182232857295580349070053 2659168660742921315450635)
    ·
      refine ⟨3988752991114381973175953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2659168660742921315450635 3988752991114381973175953)
      ·
        refine ⟨2991564743335786479881965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3988752991114381973175953 2991564743335786479881965)
        ·
          refine ⟨1121836778750919929955737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2991564743335786479881965 1121836778750919929955737)
          ·
            refine ⟨841377584063189947466803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1121836778750919929955737 841377584063189947466803)
            ·
              refine ⟨1262066376094784921200205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 841377584063189947466803 1262066376094784921200205)
              ·
                refine ⟨473274891035544345450077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1262066376094784921200205 473274891035544345450077)
                ·
                  refine ⟨177478084138329129543779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 473274891035544345450077 177478084138329129543779)
                  ·
                    rfl

theorem cell21_777684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_777684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_777684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_777684 prefixEnd_777684 := by exact prefixLift 777684
  have htrace : WordTrace (prefixWord ++ tailWord_777684) baseStart_777684 baseEnd_777684 := by
    simpa [prefixWord, tailWord_777684, baseEnd_777684] using wordTrace_append hprefix tailTrace_777684
  have hstable : (prefixWord ++ tailWord_777684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777684).length < 2 ^ (prefixWord ++ tailWord_777684).sum := by decide
  have hdescent : baseEnd_777684 < baseStart_777684 := by decide
  rcases family_descends (prefixWord ++ tailWord_777684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777723 : List Nat := [1, 1, 1, 1, 1, 3, 2, 7, 4]
def baseStart_777723 : Nat := 118140960795 + 777723 * 2 ^ 59
def prefixEnd_777723 : Nat := 4983230072969 + 3 ^ 40 * 777723 * 2
def baseEnd_777723 : Nat := 177486984469673728393699

theorem tailTrace_777723 : CollatzResearch.WordTrace tailWord_777723 prefixEnd_777723 177486984469673728393699 := by
  unfold tailWord_777723
  simp only [CollatzResearch.WordTrace]
  refine ⟨28365888161449870358809823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18910592107633246905873215 28365888161449870358809823)
  ·
    refine ⟨42548832242174805538214735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28365888161449870358809823 42548832242174805538214735)
    ·
      refine ⟨63823248363262208307322103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42548832242174805538214735 63823248363262208307322103)
      ·
        refine ⟨95734872544893312460983155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63823248363262208307322103 95734872544893312460983155)
        ·
          refine ⟨143602308817339968691474733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95734872544893312460983155 143602308817339968691474733)
          ·
            refine ⟨53850865806502488259303025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143602308817339968691474733 53850865806502488259303025)
            ·
              refine ⟨40388149354876866194477269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53850865806502488259303025 40388149354876866194477269)
              ·
                refine ⟨946597250504926551433061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 40388149354876866194477269 946597250504926551433061)
                ·
                  refine ⟨177486984469673728393699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 946597250504926551433061 177486984469673728393699)
                  ·
                    rfl

theorem cell21_777723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 4].length) (baseStart_777723 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_777723 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_777723 prefixEnd_777723 := by exact prefixLift 777723
  have htrace : WordTrace (prefixWord ++ tailWord_777723) baseStart_777723 baseEnd_777723 := by
    simpa [prefixWord, tailWord_777723, baseEnd_777723] using wordTrace_append hprefix tailTrace_777723
  have hstable : (prefixWord ++ tailWord_777723).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777723).length < 2 ^ (prefixWord ++ tailWord_777723).sum := by decide
  have hdescent : baseEnd_777723 < baseStart_777723 := by decide
  rcases family_descends (prefixWord ++ tailWord_777723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777737 : List Nat := [1, 2, 1, 1, 3, 1, 3, 9]
def baseStart_777737 : Nat := 118140960795 + 777737 * 2 ^ 59
def prefixEnd_777737 : Nat := 4983230072969 + 3 ^ 40 * 777737 * 2
def baseEnd_777737 : Nat := 59163393153470938386779

theorem tailTrace_777737 : CollatzResearch.WordTrace tailWord_777737 prefixEnd_777737 59163393153470938386779 := by
  unfold tailWord_777737
  simp only [CollatzResearch.WordTrace]
  refine ⟨28366398783399150749819465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18910932522266100499879643 28366398783399150749819465)
  ·
    refine ⟨21274799087549363062364599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28366398783399150749819465 21274799087549363062364599)
    ·
      refine ⟨31912198631324044593546899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21274799087549363062364599 31912198631324044593546899)
      ·
        refine ⟨47868297946986066890320349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31912198631324044593546899 47868297946986066890320349)
        ·
          refine ⟨17950611730119775083870131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47868297946986066890320349 17950611730119775083870131)
          ·
            refine ⟨26925917595179662625805197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17950611730119775083870131 26925917595179662625805197)
            ·
              refine ⟨10097219098192373484676949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26925917595179662625805197 10097219098192373484676949)
              ·
                refine ⟨59163393153470938386779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10097219098192373484676949 59163393153470938386779)
                ·
                  rfl

theorem cell21_777737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 9].length) (baseStart_777737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_777737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_777737 prefixEnd_777737 := by exact prefixLift 777737
  have htrace : WordTrace (prefixWord ++ tailWord_777737) baseStart_777737 baseEnd_777737 := by
    simpa [prefixWord, tailWord_777737, baseEnd_777737] using wordTrace_append hprefix tailTrace_777737
  have hstable : (prefixWord ++ tailWord_777737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777737).length < 2 ^ (prefixWord ++ tailWord_777737).sum := by decide
  have hdescent : baseEnd_777737 < baseStart_777737 := by decide
  rcases family_descends (prefixWord ++ tailWord_777737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777760 : List Nat := [2, 1, 1, 6, 1, 3, 2, 2, 3]
def baseStart_777760 : Nat := 118140960795 + 777760 * 2 ^ 59
def prefixEnd_777760 : Nat := 4983230072969 + 3 ^ 40 * 777760 * 2
def baseEnd_777760 : Nat := 177495428373769886276957

theorem tailTrace_777760 : CollatzResearch.WordTrace tailWord_777760 prefixEnd_777760 177495428373769886276957 := by
  unfold tailWord_777760
  simp only [CollatzResearch.WordTrace]
  refine ⟨14183618831157912838953367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18911491774877217118604489 14183618831157912838953367)
  ·
    refine ⟨21275428246736869258430051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14183618831157912838953367 21275428246736869258430051)
    ·
      refine ⟨31913142370105303887645077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21275428246736869258430051 31913142370105303887645077)
      ·
        refine ⟨1495928548598686119733363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31913142370105303887645077 1495928548598686119733363)
        ·
          refine ⟨2243892822898029179600045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1495928548598686119733363 2243892822898029179600045)
          ·
            refine ⟨841459808586760942350017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2243892822898029179600045 841459808586760942350017)
            ·
              refine ⟨631094856440070706762513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 841459808586760942350017 631094856440070706762513)
              ·
                refine ⟨473321142330053030071885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 631094856440070706762513 473321142330053030071885)
                ·
                  refine ⟨177495428373769886276957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 473321142330053030071885 177495428373769886276957)
                  ·
                    rfl

theorem cell21_777760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 2, 3].length) (baseStart_777760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_777760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_777760 prefixEnd_777760 := by exact prefixLift 777760
  have htrace : WordTrace (prefixWord ++ tailWord_777760) baseStart_777760 baseEnd_777760 := by
    simpa [prefixWord, tailWord_777760, baseEnd_777760] using wordTrace_append hprefix tailTrace_777760
  have hstable : (prefixWord ++ tailWord_777760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777760).length < 2 ^ (prefixWord ++ tailWord_777760).sum := by decide
  have hdescent : baseEnd_777760 < baseStart_777760 := by decide
  rcases family_descends (prefixWord ++ tailWord_777760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777785 : List Nat := [1, 2, 1, 5, 1, 3, 1, 2, 5]
def baseStart_777785 : Nat := 118140960795 + 777785 * 2 ^ 59
def prefixEnd_777785 : Nat := 4983230072969 + 3 ^ 40 * 777785 * 2
def baseEnd_777785 : Nat := 177501133714375398360239

theorem tailTrace_777785 : CollatzResearch.WordTrace tailWord_777785 prefixEnd_777785 177501133714375398360239 := by
  unfold tailWord_777785
  simp only [CollatzResearch.WordTrace]
  refine ⟨28368149487225254947566809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18912099658150169965044539 28368149487225254947566809)
  ·
    refine ⟨21276112115418941210675107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28368149487225254947566809 21276112115418941210675107)
    ·
      refine ⟨31914168173128411816012661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21276112115418941210675107 31914168173128411816012661)
      ·
        refine ⟨2991953266230788607751187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31914168173128411816012661 2991953266230788607751187)
        ·
          refine ⟨4487929899346182911626781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2991953266230788607751187 4487929899346182911626781)
          ·
            refine ⟨1682973712254818591860043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4487929899346182911626781 1682973712254818591860043)
            ·
              refine ⟨2524460568382227887790065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1682973712254818591860043 2524460568382227887790065)
              ·
                refine ⟨1893345426286670915842549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2524460568382227887790065 1893345426286670915842549)
                ·
                  refine ⟨177501133714375398360239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1893345426286670915842549 177501133714375398360239)
                  ·
                    rfl

theorem cell21_777785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 5].length) (baseStart_777785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_777785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_777785 prefixEnd_777785 := by exact prefixLift 777785
  have htrace : WordTrace (prefixWord ++ tailWord_777785) baseStart_777785 baseEnd_777785 := by
    simpa [prefixWord, tailWord_777785, baseEnd_777785] using wordTrace_append hprefix tailTrace_777785
  have hstable : (prefixWord ++ tailWord_777785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777785).length < 2 ^ (prefixWord ++ tailWord_777785).sum := by decide
  have hdescent : baseEnd_777785 < baseStart_777785 := by decide
  rcases family_descends (prefixWord ++ tailWord_777785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777802 : List Nat := [3, 1, 2, 1, 1, 3, 4, 3, 3]
def baseStart_777802 : Nat := 118140960795 + 777802 * 2 ^ 59
def prefixEnd_777802 : Nat := 4983230072969 + 3 ^ 40 * 777802 * 2
def baseEnd_777802 : Nat := 177505013345987146576871

theorem tailTrace_777802 : CollatzResearch.WordTrace tailWord_777802 prefixEnd_777802 177505013345987146576871 := by
  unfold tailWord_777802
  simp only [CollatzResearch.WordTrace]
  refine ⟨7092192382040916712733915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18912513018775777900623773 7092192382040916712733915)
  ·
    refine ⟨10638288573061375069100873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7092192382040916712733915 10638288573061375069100873)
    ·
      refine ⟨7978716429796031301825655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10638288573061375069100873 7978716429796031301825655)
      ·
        refine ⟨11968074644694046952738483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7978716429796031301825655 11968074644694046952738483)
        ·
          refine ⟨17952111967041070429107725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11968074644694046952738483 17952111967041070429107725)
          ·
            refine ⟨6732041987640401410915397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17952111967041070429107725 6732041987640401410915397)
            ·
              refine ⟨1262257872682575264546637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6732041987640401410915397 1262257872682575264546637)
              ·
                refine ⟨473346702255965724204989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1262257872682575264546637 473346702255965724204989)
                ·
                  refine ⟨177505013345987146576871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 473346702255965724204989 177505013345987146576871)
                  ·
                    rfl

theorem cell21_777802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 3, 3].length) (baseStart_777802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_777802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_777802 prefixEnd_777802 := by exact prefixLift 777802
  have htrace : WordTrace (prefixWord ++ tailWord_777802) baseStart_777802 baseEnd_777802 := by
    simpa [prefixWord, tailWord_777802, baseEnd_777802] using wordTrace_append hprefix tailTrace_777802
  have hstable : (prefixWord ++ tailWord_777802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777802).length < 2 ^ (prefixWord ++ tailWord_777802).sum := by decide
  have hdescent : baseEnd_777802 < baseStart_777802 := by decide
  rcases family_descends (prefixWord ++ tailWord_777802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777864 : List Nat := [2, 1, 3, 5, 2, 1, 7]
def baseStart_777864 : Nat := 118140960795 + 777864 * 2 ^ 59
def prefixEnd_777864 : Nat := 4983230072969 + 3 ^ 40 * 777864 * 2
def baseEnd_777864 : Nat := 19724351398965424060379

theorem tailTrace_777864 : CollatzResearch.WordTrace tailWord_777864 prefixEnd_777864 19724351398965424060379 := by
  unfold tailWord_777864
  simp only [CollatzResearch.WordTrace]
  refine ⟨14185515426969525719846323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18914020569292700959795097 14185515426969525719846323)
  ·
    refine ⟨21278273140454288579769485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14185515426969525719846323 21278273140454288579769485)
    ·
      refine ⟨7979352427670358217413557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21278273140454288579769485 7979352427670358217413557)
      ·
        refine ⟨748064290094096082882521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7979352427670358217413557 748064290094096082882521)
        ·
          refine ⟨561048217570572062161891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 748064290094096082882521 561048217570572062161891)
          ·
            refine ⟨841572326355858093242837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561048217570572062161891 841572326355858093242837)
            ·
              refine ⟨19724351398965424060379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 841572326355858093242837 19724351398965424060379)
              ·
                rfl

theorem cell21_777864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 7].length) (baseStart_777864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_777864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_777864 prefixEnd_777864 := by exact prefixLift 777864
  have htrace : WordTrace (prefixWord ++ tailWord_777864) baseStart_777864 baseEnd_777864 := by
    simpa [prefixWord, tailWord_777864, baseEnd_777864] using wordTrace_append hprefix tailTrace_777864
  have hstable : (prefixWord ++ tailWord_777864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777864).length < 2 ^ (prefixWord ++ tailWord_777864).sum := by decide
  have hdescent : baseEnd_777864 < baseStart_777864 := by decide
  rcases family_descends (prefixWord ++ tailWord_777864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777892 : List Nat := [2, 3, 1, 2, 2, 3, 1, 3, 4]
def baseStart_777892 : Nat := 118140960795 + 777892 * 2 ^ 59
def prefixEnd_777892 : Nat := 4983230072969 + 3 ^ 40 * 777892 * 2
def baseEnd_777892 : Nat := 177525552572166990076687

theorem tailTrace_777892 : CollatzResearch.WordTrace tailWord_777892 prefixEnd_777892 177525552572166990076687 := by
  unfold tailWord_777892
  simp only [CollatzResearch.WordTrace]
  refine ⟨14186026048918806110855965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18914701398558408147807953 14186026048918806110855965)
  ·
    refine ⟨5319759768344552291570987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14186026048918806110855965 5319759768344552291570987)
    ·
      refine ⟨7979639652516828437356481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5319759768344552291570987 7979639652516828437356481)
      ·
        refine ⟨5984729739387621328017361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7979639652516828437356481 5984729739387621328017361)
        ·
          refine ⟨4488547304540715996013021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5984729739387621328017361 4488547304540715996013021)
          ·
            refine ⟨1683205239202768498504883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4488547304540715996013021 1683205239202768498504883)
            ·
              refine ⟨2524807858804152747757325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1683205239202768498504883 2524807858804152747757325)
              ·
                refine ⟨946802947051557280408997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2524807858804152747757325 946802947051557280408997)
                ·
                  refine ⟨177525552572166990076687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 946802947051557280408997 177525552572166990076687)
                  ·
                    rfl

theorem cell21_777892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_777892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_777892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_777892 prefixEnd_777892 := by exact prefixLift 777892
  have htrace : WordTrace (prefixWord ++ tailWord_777892) baseStart_777892 baseEnd_777892 := by
    simpa [prefixWord, tailWord_777892, baseEnd_777892] using wordTrace_append hprefix tailTrace_777892
  have hstable : (prefixWord ++ tailWord_777892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777892).length < 2 ^ (prefixWord ++ tailWord_777892).sum := by decide
  have hdescent : baseEnd_777892 < baseStart_777892 := by decide
  rcases family_descends (prefixWord ++ tailWord_777892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777926 : List Nat := [6, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_777926 : Nat := 118140960795 + 777926 * 2 ^ 59
def prefixEnd_777926 : Nat := 4983230072969 + 3 ^ 40 * 777926 * 2
def baseEnd_777926 : Nat := 177533311835390486509951

theorem tailTrace_777926 : CollatzResearch.WordTrace tailWord_777926 prefixEnd_777926 177533311835390486509951 := by
  unfold tailWord_777926
  simp only [CollatzResearch.WordTrace]
  refine ⟨886665380616076125889051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18915528119809624018966421 886665380616076125889051)
  ·
    refine ⟨1329998070924114188833577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 886665380616076125889051 1329998070924114188833577)
    ·
      refine ⟨997498553193085641625183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1329998070924114188833577 997498553193085641625183)
      ·
        refine ⟨1496247829789628462437775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 997498553193085641625183 1496247829789628462437775)
        ·
          refine ⟨2244371744684442693656663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1496247829789628462437775 2244371744684442693656663)
          ·
            refine ⟨3366557617026664040484995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2244371744684442693656663 3366557617026664040484995)
            ·
              refine ⟨5049836425539996060727493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3366557617026664040484995 5049836425539996060727493)
              ·
                refine ⟨946844329788749261386405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5049836425539996060727493 946844329788749261386405)
                ·
                  refine ⟨177533311835390486509951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 946844329788749261386405 177533311835390486509951)
                  ·
                    rfl

theorem cell21_777926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_777926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_777926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_777926 prefixEnd_777926 := by exact prefixLift 777926
  have htrace : WordTrace (prefixWord ++ tailWord_777926) baseStart_777926 baseEnd_777926 := by
    simpa [prefixWord, tailWord_777926, baseEnd_777926] using wordTrace_append hprefix tailTrace_777926
  have hstable : (prefixWord ++ tailWord_777926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777926).length < 2 ^ (prefixWord ++ tailWord_777926).sum := by decide
  have hdescent : baseEnd_777926 < baseStart_777926 := by decide
  rcases family_descends (prefixWord ++ tailWord_777926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777951 : List Nat := [1, 1, 2, 3, 2, 2, 1, 5, 4]
def baseStart_777951 : Nat := 118140960795 + 777951 * 2 ^ 59
def prefixEnd_777951 : Nat := 4983230072969 + 3 ^ 40 * 777951 * 2
def baseEnd_777951 : Nat := 177539017175995998593233

theorem tailTrace_777951 : CollatzResearch.WordTrace tailWord_777951 prefixEnd_777951 177539017175995998593233 := by
  unfold tailWord_777951
  simp only [CollatzResearch.WordTrace]
  refine ⟨28374204004623865298109707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18916136003082576865406471 28374204004623865298109707)
  ·
    refine ⟨42561306006935797947164561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28374204004623865298109707 42561306006935797947164561)
    ·
      refine ⟨31920979505201848460373421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42561306006935797947164561 31920979505201848460373421)
      ·
        refine ⟨11970367314450693172640033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31920979505201848460373421 11970367314450693172640033)
        ·
          refine ⟨8977775485838019879480025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11970367314450693172640033 8977775485838019879480025)
          ·
            refine ⟨6733331614378514909610019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8977775485838019879480025 6733331614378514909610019)
            ·
              refine ⟨10099997421567772364415029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6733331614378514909610019 10099997421567772364415029)
              ·
                refine ⟨946874758271978659163909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10099997421567772364415029 946874758271978659163909)
                ·
                  refine ⟨177539017175995998593233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 946874758271978659163909 177539017175995998593233)
                  ·
                    rfl

theorem cell21_777951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 4].length) (baseStart_777951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_777951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_777951 prefixEnd_777951 := by exact prefixLift 777951
  have htrace : WordTrace (prefixWord ++ tailWord_777951) baseStart_777951 baseEnd_777951 := by
    simpa [prefixWord, tailWord_777951, baseEnd_777951] using wordTrace_append hprefix tailTrace_777951
  have hstable : (prefixWord ++ tailWord_777951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777951).length < 2 ^ (prefixWord ++ tailWord_777951).sum := by decide
  have hdescent : baseEnd_777951 < baseStart_777951 := by decide
  rcases family_descends (prefixWord ++ tailWord_777951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777996 : List Nat := [2, 2, 1, 2, 2, 1, 3, 3, 5]
def baseStart_777996 : Nat := 118140960795 + 777996 * 2 ^ 59
def prefixEnd_777996 : Nat := 4983230072969 + 3 ^ 40 * 777996 * 2
def baseEnd_777996 : Nat := 177549286789085920343141

theorem tailTrace_777996 : CollatzResearch.WordTrace tailWord_777996 prefixEnd_777996 177549286789085920343141 := by
  unfold tailWord_777996
  simp only [CollatzResearch.WordTrace]
  refine ⟨14187922644730418991748921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18917230192973891988998561 14187922644730418991748921)
  ·
    refine ⟨10640941983547814243811691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14187922644730418991748921 10640941983547814243811691)
    ·
      refine ⟨15961412975321721365717537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10640941983547814243811691 15961412975321721365717537)
      ·
        refine ⟨11971059731491291024288153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15961412975321721365717537 11971059731491291024288153)
        ·
          refine ⟨8978294798618468268216115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11971059731491291024288153 8978294798618468268216115)
          ·
            refine ⟨13467442197927702402324173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8978294798618468268216115 13467442197927702402324173)
            ·
              refine ⟨5050290824222888400871565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13467442197927702402324173 5050290824222888400871565)
              ·
                refine ⟨1893859059083583150326837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5050290824222888400871565 1893859059083583150326837)
                ·
                  refine ⟨177549286789085920343141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1893859059083583150326837 177549286789085920343141)
                  ·
                    rfl

theorem cell21_777996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_777996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_777996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_777996 prefixEnd_777996 := by exact prefixLift 777996
  have htrace : WordTrace (prefixWord ++ tailWord_777996) baseStart_777996 baseEnd_777996 := by
    simpa [prefixWord, tailWord_777996, baseEnd_777996] using wordTrace_append hprefix tailTrace_777996
  have hstable : (prefixWord ++ tailWord_777996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777996).length < 2 ^ (prefixWord ++ tailWord_777996).sum := by decide
  have hdescent : baseEnd_777996 < baseStart_777996 := by decide
  rcases family_descends (prefixWord ++ tailWord_777996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778002 : List Nat := [3, 2, 4, 1, 1, 2, 3, 1, 4]
def baseStart_778002 : Nat := 118140960795 + 778002 * 2 ^ 59
def prefixEnd_778002 : Nat := 4983230072969 + 3 ^ 40 * 778002 * 2
def baseEnd_778002 : Nat := 177550656070831243243129

theorem tailTrace_778002 : CollatzResearch.WordTrace tailWord_778002 prefixEnd_778002 177550656070831243243129 := by
  unfold tailWord_778002
  simp only [CollatzResearch.WordTrace]
  refine ⟨7094016031859775252054065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18917376084959400672144173 7094016031859775252054065)
  ·
    refine ⟨5320512023894831439040549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7094016031859775252054065 5320512023894831439040549)
    ·
      refine ⟨997596004480280894820103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5320512023894831439040549 997596004480280894820103)
      ·
        refine ⟨1496394006720421342230155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 997596004480280894820103 1496394006720421342230155)
        ·
          refine ⟨2244591010080632013345233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1496394006720421342230155 2244591010080632013345233)
          ·
            refine ⟨1683443257560474010008925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2244591010080632013345233 1683443257560474010008925)
            ·
              refine ⟨631291221585177753753347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1683443257560474010008925 631291221585177753753347)
              ·
                refine ⟨946936832377766630630021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631291221585177753753347 946936832377766630630021)
                ·
                  refine ⟨177550656070831243243129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 946936832377766630630021 177550656070831243243129)
                  ·
                    rfl

theorem cell21_778002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_778002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_778002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_778002 prefixEnd_778002 := by exact prefixLift 778002
  have htrace : WordTrace (prefixWord ++ tailWord_778002) baseStart_778002 baseEnd_778002 := by
    simpa [prefixWord, tailWord_778002, baseEnd_778002] using wordTrace_append hprefix tailTrace_778002
  have hstable : (prefixWord ++ tailWord_778002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778002).length < 2 ^ (prefixWord ++ tailWord_778002).sum := by decide
  have hdescent : baseEnd_778002 < baseStart_778002 := by decide
  rcases family_descends (prefixWord ++ tailWord_778002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778047 : List Nat := [1, 1, 2, 2, 6, 1, 3, 2, 3]
def baseStart_778047 : Nat := 118140960795 + 778047 * 2 ^ 59
def prefixEnd_778047 : Nat := 4983230072969 + 3 ^ 40 * 778047 * 2
def baseEnd_778047 : Nat := 177560925683921164993037

theorem tailTrace_778047 : CollatzResearch.WordTrace tailWord_778047 prefixEnd_778047 177560925683921164993037 := by
  unfold tailWord_778047
  simp only [CollatzResearch.WordTrace]
  refine ⟨28377705412276073693604395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18918470274850715795736263 28377705412276073693604395)
  ·
    refine ⟨42566558118414110540406593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28377705412276073693604395 42566558118414110540406593)
    ·
      refine ⟨31924918588810582905304945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42566558118414110540406593 31924918588810582905304945)
      ·
        refine ⟨23943688941607937178978709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31924918588810582905304945 23943688941607937178978709)
        ·
          refine ⟨1122360419137872055264627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23943688941607937178978709 1122360419137872055264627)
          ·
            refine ⟨1683540628706808082896941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1122360419137872055264627 1683540628706808082896941)
            ·
              refine ⟨631327735765053031086353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1683540628706808082896941 631327735765053031086353)
              ·
                refine ⟨473495801823789773314765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 631327735765053031086353 473495801823789773314765)
                ·
                  refine ⟨177560925683921164993037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 473495801823789773314765 177560925683921164993037)
                  ·
                    rfl

theorem cell21_778047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 2, 3].length) (baseStart_778047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_778047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_778047 prefixEnd_778047 := by exact prefixLift 778047
  have htrace : WordTrace (prefixWord ++ tailWord_778047) baseStart_778047 baseEnd_778047 := by
    simpa [prefixWord, tailWord_778047, baseEnd_778047] using wordTrace_append hprefix tailTrace_778047
  have hstable : (prefixWord ++ tailWord_778047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778047).length < 2 ^ (prefixWord ++ tailWord_778047).sum := by decide
  have hdescent : baseEnd_778047 < baseStart_778047 := by decide
  rcases family_descends (prefixWord ++ tailWord_778047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778061 : List Nat := [1, 6, 1, 2, 1, 2, 1, 3, 4]
def baseStart_778061 : Nat := 118140960795 + 778061 * 2 ^ 59
def prefixEnd_778061 : Nat := 4983230072969 + 3 ^ 40 * 778061 * 2
def baseEnd_778061 : Nat := 177564120674660251759675

theorem tailTrace_778061 : CollatzResearch.WordTrace tailWord_778061 prefixEnd_778061 177564120674660251759675 := by
  unfold tailWord_778061
  simp only [CollatzResearch.WordTrace]
  refine ⟨28378216034225354084614037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18918810689483569389742691 28378216034225354084614037)
  ·
    refine ⟨1330228876604313472716283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28378216034225354084614037 1330228876604313472716283)
    ·
      refine ⟨1995343314906470209074425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1330228876604313472716283 1995343314906470209074425)
      ·
        refine ⟨1496507486179852656805819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1995343314906470209074425 1496507486179852656805819)
        ·
          refine ⟨2244761229269778985208729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1496507486179852656805819 2244761229269778985208729)
          ·
            refine ⟨1683570921952334238906547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2244761229269778985208729 1683570921952334238906547)
            ·
              refine ⟨2525356382928501358359821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1683570921952334238906547 2525356382928501358359821)
              ·
                refine ⟨947008643598188009384933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2525356382928501358359821 947008643598188009384933)
                ·
                  refine ⟨177564120674660251759675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 947008643598188009384933 177564120674660251759675)
                  ·
                    rfl

theorem cell21_778061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_778061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_778061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_778061 prefixEnd_778061 := by exact prefixLift 778061
  have htrace : WordTrace (prefixWord ++ tailWord_778061) baseStart_778061 baseEnd_778061 := by
    simpa [prefixWord, tailWord_778061, baseEnd_778061] using wordTrace_append hprefix tailTrace_778061
  have hstable : (prefixWord ++ tailWord_778061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778061).length < 2 ^ (prefixWord ++ tailWord_778061).sum := by decide
  have hdescent : baseEnd_778061 < baseStart_778061 := by decide
  rcases family_descends (prefixWord ++ tailWord_778061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778106 : List Nat := [3, 1, 1, 1, 1, 1, 8, 2, 3]
def baseStart_778106 : Nat := 118140960795 + 778106 * 2 ^ 59
def prefixEnd_778106 : Nat := 4983230072969 + 3 ^ 40 * 778106 * 2
def baseEnd_778106 : Nat := 177574390287750173509583

theorem tailTrace_778106 : CollatzResearch.WordTrace tailWord_778106 prefixEnd_778106 177574390287750173509583 := by
  unfold tailWord_778106
  simp only [CollatzResearch.WordTrace]
  refine ⟨7094964329765581692500543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18919904879374884513334781 7094964329765581692500543)
  ·
    refine ⟨10642446494648372538750815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7094964329765581692500543 10642446494648372538750815)
    ·
      refine ⟨15963669741972558808126223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10642446494648372538750815 15963669741972558808126223)
      ·
        refine ⟨23945504612958838212189335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15963669741972558808126223 23945504612958838212189335)
        ·
          refine ⟨35918256919438257318284003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23945504612958838212189335 35918256919438257318284003)
          ·
            refine ⟨53877385379157385977426005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35918256919438257318284003 53877385379157385977426005)
            ·
              refine ⟨631375609912000616922961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 53877385379157385977426005 631375609912000616922961)
              ·
                refine ⟨473531707434000462692221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 631375609912000616922961 473531707434000462692221)
                ·
                  refine ⟨177574390287750173509583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 473531707434000462692221 177574390287750173509583)
                  ·
                    rfl

theorem cell21_778106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 2, 3].length) (baseStart_778106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_778106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_778106 prefixEnd_778106 := by exact prefixLift 778106
  have htrace : WordTrace (prefixWord ++ tailWord_778106) baseStart_778106 baseEnd_778106 := by
    simpa [prefixWord, tailWord_778106, baseEnd_778106] using wordTrace_append hprefix tailTrace_778106
  have hstable : (prefixWord ++ tailWord_778106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778106).length < 2 ^ (prefixWord ++ tailWord_778106).sum := by decide
  have hdescent : baseEnd_778106 < baseStart_778106 := by decide
  rcases family_descends (prefixWord ++ tailWord_778106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778165 : List Nat := [1, 3, 3, 2, 1, 3, 2, 1, 5]
def baseStart_778165 : Nat := 118140960795 + 778165 * 2 ^ 59
def prefixEnd_778165 : Nat := 4983230072969 + 3 ^ 40 * 778165 * 2
def baseEnd_778165 : Nat := 177587854891579182026129

theorem tailTrace_778165 : CollatzResearch.WordTrace tailWord_778165 prefixEnd_778165 177587854891579182026129 := by
  unfold tailWord_778165
  simp only [CollatzResearch.WordTrace]
  refine ⟨28382009225848579846399949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18921339483899053230933299 28382009225848579846399949)
  ·
    refine ⟨10643253459693217442399981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28382009225848579846399949 10643253459693217442399981)
    ·
      refine ⟨3991220047384956540899993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10643253459693217442399981 3991220047384956540899993)
      ·
        refine ⟨2993415035538717405674995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3991220047384956540899993 2993415035538717405674995)
        ·
          refine ⟨4490122553308076108512493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2993415035538717405674995 4490122553308076108512493)
          ·
            refine ⟨1683795957490528540692185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4490122553308076108512493 1683795957490528540692185)
            ·
              refine ⟨1262846968117896405519139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1683795957490528540692185 1262846968117896405519139)
              ·
                refine ⟨1894270452176844608278709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1262846968117896405519139 1894270452176844608278709)
                ·
                  refine ⟨177587854891579182026129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1894270452176844608278709 177587854891579182026129)
                  ·
                    rfl

theorem cell21_778165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_778165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_778165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_778165 prefixEnd_778165 := by exact prefixLift 778165
  have htrace : WordTrace (prefixWord ++ tailWord_778165) baseStart_778165 baseEnd_778165 := by
    simpa [prefixWord, tailWord_778165, baseEnd_778165] using wordTrace_append hprefix tailTrace_778165
  have hstable : (prefixWord ++ tailWord_778165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778165).length < 2 ^ (prefixWord ++ tailWord_778165).sum := by decide
  have hdescent : baseEnd_778165 < baseStart_778165 := by decide
  rcases family_descends (prefixWord ++ tailWord_778165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778224 : List Nat := [2, 1, 1, 1, 3, 2, 5, 1, 5]
def baseStart_778224 : Nat := 118140960795 + 778224 * 2 ^ 59
def prefixEnd_778224 : Nat := 4983230072969 + 3 ^ 40 * 778224 * 2
def baseEnd_778224 : Nat := 177601319495408190542675

theorem tailTrace_778224 : CollatzResearch.WordTrace tailWord_778224 prefixEnd_778224 177601319495408190542675 := by
  unfold tailWord_778224
  simp only [CollatzResearch.WordTrace]
  refine ⟨14192080566317416461398863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18922774088423221948531817 14192080566317416461398863)
  ·
    refine ⟨21288120849476124692098295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14192080566317416461398863 21288120849476124692098295)
    ·
      refine ⟨31932181274214187038147443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21288120849476124692098295 31932181274214187038147443)
      ·
        refine ⟨47898271911321280557221165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31932181274214187038147443 47898271911321280557221165)
        ·
          refine ⟨17961851966745480208957937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47898271911321280557221165 17961851966745480208957937)
          ·
            refine ⟨13471388975059110156718453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17961851966745480208957937 13471388975059110156718453)
            ·
              refine ⟨1262942716411791577192355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13471388975059110156718453 1262942716411791577192355)
              ·
                refine ⟨1894414074617687365788533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1262942716411791577192355 1894414074617687365788533)
                ·
                  refine ⟨177601319495408190542675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1894414074617687365788533 177601319495408190542675)
                  ·
                    rfl

theorem cell21_778224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 5].length) (baseStart_778224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_778224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_778224 prefixEnd_778224 := by exact prefixLift 778224
  have htrace : WordTrace (prefixWord ++ tailWord_778224) baseStart_778224 baseEnd_778224 := by
    simpa [prefixWord, tailWord_778224, baseEnd_778224] using wordTrace_append hprefix tailTrace_778224
  have hstable : (prefixWord ++ tailWord_778224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778224).length < 2 ^ (prefixWord ++ tailWord_778224).sum := by decide
  have hdescent : baseEnd_778224 < baseStart_778224 := by decide
  rcases family_descends (prefixWord ++ tailWord_778224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778230 : List Nat := [5, 1, 1, 1, 4, 2, 2, 1, 4]
def baseStart_778230 : Nat := 118140960795 + 778230 * 2 ^ 59
def prefixEnd_778230 : Nat := 4983230072969 + 3 ^ 40 * 778230 * 2
def baseEnd_778230 : Nat := 177602688777153513442663

theorem tailTrace_778230 : CollatzResearch.WordTrace tailWord_778230 prefixEnd_778230 177602688777153513442663 := by
  unfold tailWord_778230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1774023748163318496719759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18922919980408730631677429 1774023748163318496719759)
  ·
    refine ⟨2661035622244977745079639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1774023748163318496719759 2661035622244977745079639)
    ·
      refine ⟨3991553433367466617619459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2661035622244977745079639 3991553433367466617619459)
      ·
        refine ⟨5987330150051199926429189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3991553433367466617619459 5987330150051199926429189)
        ·
          refine ⟨1122624403134599986205473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5987330150051199926429189 1122624403134599986205473)
          ·
            refine ⟨841968302350949989654105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1122624403134599986205473 841968302350949989654105)
            ·
              refine ⟨631476226763212492240579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 841968302350949989654105 631476226763212492240579)
              ·
                refine ⟨947214340144818738360869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631476226763212492240579 947214340144818738360869)
                ·
                  refine ⟨177602688777153513442663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 947214340144818738360869 177602688777153513442663)
                  ·
                    rfl

theorem cell21_778230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_778230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_778230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_778230 prefixEnd_778230 := by exact prefixLift 778230
  have htrace : WordTrace (prefixWord ++ tailWord_778230) baseStart_778230 baseEnd_778230 := by
    simpa [prefixWord, tailWord_778230, baseEnd_778230] using wordTrace_append hprefix tailTrace_778230
  have hstable : (prefixWord ++ tailWord_778230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778230).length < 2 ^ (prefixWord ++ tailWord_778230).sum := by decide
  have hdescent : baseEnd_778230 < baseStart_778230 := by decide
  rcases family_descends (prefixWord ++ tailWord_778230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778269 : List Nat := [1, 4, 2, 2, 2, 10]
def baseStart_778269 : Nat := 118140960795 + 778269 * 2 ^ 59
def prefixEnd_778269 : Nat := 4983230072969 + 3 ^ 40 * 778269 * 2
def baseEnd_778269 : Nat := 6578207004018448603429

theorem tailTrace_778269 : CollatzResearch.WordTrace tailWord_778269 prefixEnd_778269 6578207004018448603429 := by
  unfold tailWord_778269
  simp only [CollatzResearch.WordTrace]
  refine ⟨28385802417471805608185861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18923868278314537072123907 28385802417471805608185861)
  ·
    refine ⟨5322337953275963551534849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28385802417471805608185861 5322337953275963551534849)
    ·
      refine ⟨3991753464956972663651137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5322337953275963551534849 3991753464956972663651137)
      ·
        refine ⟨2993815098717729497738353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3991753464956972663651137 2993815098717729497738353)
        ·
          refine ⟨2245361324038297123303765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2993815098717729497738353 2245361324038297123303765)
          ·
            refine ⟨6578207004018448603429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2245361324038297123303765 6578207004018448603429)
            ·
              rfl

theorem cell21_778269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 10].length) (baseStart_778269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_778269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_778269 prefixEnd_778269 := by exact prefixLift 778269
  have htrace : WordTrace (prefixWord ++ tailWord_778269) baseStart_778269 baseEnd_778269 := by
    simpa [prefixWord, tailWord_778269, baseEnd_778269] using wordTrace_append hprefix tailTrace_778269
  have hstable : (prefixWord ++ tailWord_778269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778269).length < 2 ^ (prefixWord ++ tailWord_778269).sum := by decide
  have hdescent : baseEnd_778269 < baseStart_778269 := by decide
  rcases family_descends (prefixWord ++ tailWord_778269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778286 : List Nat := [4, 1, 3, 1, 1, 2, 3, 6]
def baseStart_778286 : Nat := 118140960795 + 778286 * 2 ^ 59
def prefixEnd_778286 : Nat := 4983230072969 + 3 ^ 40 * 778286 * 2
def baseEnd_778286 : Nat := 59205156246703286836405

theorem tailTrace_778286 : CollatzResearch.WordTrace tailWord_778286 prefixEnd_778286 59205156246703286836405 := by
  unfold tailWord_778286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3548302807301277188944339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18924281638940145007703141 3548302807301277188944339)
  ·
    refine ⟨5322454210951915783416509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3548302807301277188944339 5322454210951915783416509)
    ·
      refine ⟨1995920329106968418781191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5322454210951915783416509 1995920329106968418781191)
      ·
        refine ⟨2993880493660452628171787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1995920329106968418781191 2993880493660452628171787)
        ·
          refine ⟨4490820740490678942257681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2993880493660452628171787 4490820740490678942257681)
          ·
            refine ⟨3368115555368009206693261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4490820740490678942257681 3368115555368009206693261)
            ·
              refine ⟨1263043333263003452509973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3368115555368009206693261 1263043333263003452509973)
              ·
                refine ⟨59205156246703286836405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1263043333263003452509973 59205156246703286836405)
                ·
                  rfl

theorem cell21_778286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_778286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_778286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_778286 prefixEnd_778286 := by exact prefixLift 778286
  have htrace : WordTrace (prefixWord ++ tailWord_778286) baseStart_778286 baseEnd_778286 := by
    simpa [prefixWord, tailWord_778286, baseEnd_778286] using wordTrace_append hprefix tailTrace_778286
  have hstable : (prefixWord ++ tailWord_778286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778286).length < 2 ^ (prefixWord ++ tailWord_778286).sum := by decide
  have hdescent : baseEnd_778286 < baseStart_778286 := by decide
  rcases family_descends (prefixWord ++ tailWord_778286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778300 : List Nat := [2, 2, 2, 2, 2, 1, 3, 2, 5]
def baseStart_778300 : Nat := 118140960795 + 778300 * 2 ^ 59
def prefixEnd_778300 : Nat := 4983230072969 + 3 ^ 40 * 778300 * 2
def baseEnd_778300 : Nat := 177618663730848947275853

theorem tailTrace_778300 : CollatzResearch.WordTrace tailWord_778300 prefixEnd_778300 177618663730848947275853 := by
  unfold tailWord_778300
  simp only [CollatzResearch.WordTrace]
  refine ⟨14193466540179748951282177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18924622053572998601709569 14193466540179748951282177)
  ·
    refine ⟨10645099905134811713461633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14193466540179748951282177 10645099905134811713461633)
    ·
      refine ⟨7983824928851108785096225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10645099905134811713461633 7983824928851108785096225)
      ·
        refine ⟨5987868696638331588822169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7983824928851108785096225 5987868696638331588822169)
        ·
          refine ⟨4490901522478748691616627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5987868696638331588822169 4490901522478748691616627)
          ·
            refine ⟨6736352283718123037424941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4490901522478748691616627 6736352283718123037424941)
            ·
              refine ⟨2526132106394296139034353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6736352283718123037424941 2526132106394296139034353)
              ·
                refine ⟨1894599079795722104275765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2526132106394296139034353 1894599079795722104275765)
                ·
                  refine ⟨177618663730848947275853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1894599079795722104275765 177618663730848947275853)
                  ·
                    rfl

theorem cell21_778300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_778300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_778300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_778300 prefixEnd_778300 := by exact prefixLift 778300
  have htrace : WordTrace (prefixWord ++ tailWord_778300) baseStart_778300 baseEnd_778300 := by
    simpa [prefixWord, tailWord_778300, baseEnd_778300] using wordTrace_append hprefix tailTrace_778300
  have hstable : (prefixWord ++ tailWord_778300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778300).length < 2 ^ (prefixWord ++ tailWord_778300).sum := by decide
  have hdescent : baseEnd_778300 < baseStart_778300 := by decide
  rcases family_descends (prefixWord ++ tailWord_778300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778314 : List Nat := [3, 1, 2, 1, 1, 2, 1, 4, 6]
def baseStart_778314 : Nat := 118140960795 + 778314 * 2 ^ 59
def prefixEnd_778314 : Nat := 4983230072969 + 3 ^ 40 * 778314 * 2
def baseEnd_778314 : Nat := 177621858721588034042491

theorem tailTrace_778314 : CollatzResearch.WordTrace tailWord_778314 prefixEnd_778314 177621858721588034042491 := by
  unfold tailWord_778314
  simp only [CollatzResearch.WordTrace]
  refine ⟨7096860925577194573393499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18924962468205852195715997 7096860925577194573393499)
  ·
    refine ⟨10645291388365791860090249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7096860925577194573393499 10645291388365791860090249)
    ·
      refine ⟨7983968541274343895067687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10645291388365791860090249 7983968541274343895067687)
      ·
        refine ⟨11975952811911515842601531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7983968541274343895067687 11975952811911515842601531)
        ·
          refine ⟨17963929217867273763902297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11975952811911515842601531 17963929217867273763902297)
          ·
            refine ⟨13472946913400455322926723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17963929217867273763902297 13472946913400455322926723)
            ·
              refine ⟨20209420370100682984390085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13472946913400455322926723 20209420370100682984390085)
              ·
                refine ⟨3789266319393878059573141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20209420370100682984390085 3789266319393878059573141)
                ·
                  refine ⟨177621858721588034042491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3789266319393878059573141 177621858721588034042491)
                  ·
                    rfl

theorem cell21_778314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_778314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_778314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_778314 prefixEnd_778314 := by exact prefixLift 778314
  have htrace : WordTrace (prefixWord ++ tailWord_778314) baseStart_778314 baseEnd_778314 := by
    simpa [prefixWord, tailWord_778314, baseEnd_778314] using wordTrace_append hprefix tailTrace_778314
  have hstable : (prefixWord ++ tailWord_778314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778314).length < 2 ^ (prefixWord ++ tailWord_778314).sum := by decide
  have hdescent : baseEnd_778314 < baseStart_778314 := by decide
  rcases family_descends (prefixWord ++ tailWord_778314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778348 : List Nat := [2, 2, 1, 1, 3, 4, 3, 1, 4]
def baseStart_778348 : Nat := 118140960795 + 778348 * 2 ^ 59
def prefixEnd_778348 : Nat := 4983230072969 + 3 ^ 40 * 778348 * 2
def baseEnd_778348 : Nat := 177629617984811530475755

theorem tailTrace_778348 : CollatzResearch.WordTrace tailWord_778348 prefixEnd_778348 177629617984811530475755 := by
  unfold tailWord_778348
  simp only [CollatzResearch.WordTrace]
  refine ⟨14194341892092801050155849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18925789189457068066874465 14194341892092801050155849)
  ·
    refine ⟨10645756419069600787616887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14194341892092801050155849 10645756419069600787616887)
    ·
      refine ⟨15968634628604401181425331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10645756419069600787616887 15968634628604401181425331)
      ·
        refine ⟨23952951942906601772137997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15968634628604401181425331 23952951942906601772137997)
        ·
          refine ⟨8982356978589975664551749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23952951942906601772137997 8982356978589975664551749)
          ·
            refine ⟨1684191933485620437103453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8982356978589975664551749 1684191933485620437103453)
            ·
              refine ⟨631571975057107663913795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1684191933485620437103453 631571975057107663913795)
              ·
                refine ⟨947357962585661495870693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631571975057107663913795 947357962585661495870693)
                ·
                  refine ⟨177629617984811530475755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 947357962585661495870693 177629617984811530475755)
                  ·
                    rfl

theorem cell21_778348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_778348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_778348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_778348 prefixEnd_778348 := by exact prefixLift 778348
  have htrace : WordTrace (prefixWord ++ tailWord_778348) baseStart_778348 baseEnd_778348 := by
    simpa [prefixWord, tailWord_778348, baseEnd_778348] using wordTrace_append hprefix tailTrace_778348
  have hstable : (prefixWord ++ tailWord_778348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778348).length < 2 ^ (prefixWord ++ tailWord_778348).sum := by decide
  have hdescent : baseEnd_778348 < baseStart_778348 := by decide
  rcases family_descends (prefixWord ++ tailWord_778348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778438 : List Nat := [6, 1, 2, 12]
def baseStart_778438 : Nat := 118140960795 + 778438 * 2 ^ 59
def prefixEnd_778438 : Nat := 4983230072969 + 3 ^ 40 * 778438 * 2
def baseEnd_778438 : Nat := 731070605806548864097

theorem tailTrace_778438 : CollatzResearch.WordTrace tailWord_778438 prefixEnd_778438 731070605806548864097 := by
  unfold tailWord_778438
  simp only [CollatzResearch.WordTrace]
  refine ⟨887248948558110858471499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18927977569239698314058645 887248948558110858471499)
  ·
    refine ⟨1330873422837166287707249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 887248948558110858471499 1330873422837166287707249)
    ·
      refine ⟨998155067127874715780437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1330873422837166287707249 998155067127874715780437)
      ·
        refine ⟨731070605806548864097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 998155067127874715780437 731070605806548864097)
        ·
          rfl

theorem cell21_778438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 12].length) (baseStart_778438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_778438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_778438 prefixEnd_778438 := by exact prefixLift 778438
  have htrace : WordTrace (prefixWord ++ tailWord_778438) baseStart_778438 baseEnd_778438 := by
    simpa [prefixWord, tailWord_778438, baseEnd_778438] using wordTrace_append hprefix tailTrace_778438
  have hstable : (prefixWord ++ tailWord_778438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778438).length < 2 ^ (prefixWord ++ tailWord_778438).sum := by decide
  have hdescent : baseEnd_778438 < baseStart_778438 := by decide
  rcases family_descends (prefixWord ++ tailWord_778438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778444 : List Nat := [2, 2, 1, 6, 1, 2, 2, 2, 3]
def baseStart_778444 : Nat := 118140960795 + 778444 * 2 ^ 59
def prefixEnd_778444 : Nat := 4983230072969 + 3 ^ 40 * 778444 * 2
def baseEnd_778444 : Nat := 177651526492736696875559

theorem tailTrace_778444 : CollatzResearch.WordTrace tailWord_778444 prefixEnd_778444 177651526492736696875559 := by
  unfold tailWord_778444
  simp only [CollatzResearch.WordTrace]
  refine ⟨14196092595918905247903193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18928123461225206997204257 14196092595918905247903193)
  ·
    refine ⟨10647069446939178935927395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14196092595918905247903193 10647069446939178935927395)
    ·
      refine ⟨15970604170408768403891093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10647069446939178935927395 15970604170408768403891093)
      ·
        refine ⟨748622070487911018932395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15970604170408768403891093 748622070487911018932395)
        ·
          refine ⟨1122933105731866528398593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 748622070487911018932395 1122933105731866528398593)
          ·
            refine ⟨842199829298899896298945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1122933105731866528398593 842199829298899896298945)
            ·
              refine ⟨631649871974174922224209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 842199829298899896298945 631649871974174922224209)
              ·
                refine ⟨473737403980631191668157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 631649871974174922224209 473737403980631191668157)
                ·
                  refine ⟨177651526492736696875559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 473737403980631191668157 177651526492736696875559)
                  ·
                    rfl

theorem cell21_778444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 2, 3].length) (baseStart_778444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_778444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_778444 prefixEnd_778444 := by exact prefixLift 778444
  have htrace : WordTrace (prefixWord ++ tailWord_778444) baseStart_778444 baseEnd_778444 := by
    simpa [prefixWord, tailWord_778444, baseEnd_778444] using wordTrace_append hprefix tailTrace_778444
  have hstable : (prefixWord ++ tailWord_778444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778444).length < 2 ^ (prefixWord ++ tailWord_778444).sum := by decide
  have hdescent : baseEnd_778444 < baseStart_778444 := by decide
  rcases family_descends (prefixWord ++ tailWord_778444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778480 : List Nat := [2, 1, 1, 1, 3, 1, 1, 11]
def baseStart_778480 : Nat := 118140960795 + 778480 * 2 ^ 59
def prefixEnd_778480 : Nat := 4983230072969 + 3 ^ 40 * 778480 * 2
def baseEnd_778480 : Nat := 59219914061069544758495

theorem tailTrace_778480 : CollatzResearch.WordTrace tailWord_778480 prefixEnd_778480 59219914061069544758495 := by
  unfold tailWord_778480
  simp only [CollatzResearch.WordTrace]
  refine ⟨14196749109853694322058447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18928998813138259096077929 14196749109853694322058447)
  ·
    refine ⟨21295123664780541483087671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14196749109853694322058447 21295123664780541483087671)
    ·
      refine ⟨31942685497170812224631507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21295123664780541483087671 31942685497170812224631507)
      ·
        refine ⟨47914028245756218336947261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31942685497170812224631507 47914028245756218336947261)
        ·
          refine ⟨17967760592158581876355223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47914028245756218336947261 17967760592158581876355223)
          ·
            refine ⟨26951640888237872814532835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17967760592158581876355223 26951640888237872814532835)
            ·
              refine ⟨40427461332356809221799253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26951640888237872814532835 40427461332356809221799253)
              ·
                refine ⟨59219914061069544758495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 40427461332356809221799253 59219914061069544758495)
                ·
                  rfl

theorem cell21_778480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 11].length) (baseStart_778480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_778480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_778480 prefixEnd_778480 := by exact prefixLift 778480
  have htrace : WordTrace (prefixWord ++ tailWord_778480) baseStart_778480 baseEnd_778480 := by
    simpa [prefixWord, tailWord_778480, baseEnd_778480] using wordTrace_append hprefix tailTrace_778480
  have hstable : (prefixWord ++ tailWord_778480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778480).length < 2 ^ (prefixWord ++ tailWord_778480).sum := by decide
  have hdescent : baseEnd_778480 < baseStart_778480 := by decide
  rcases family_descends (prefixWord ++ tailWord_778480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778528 : List Nat := [2, 1, 1, 5, 2, 1, 2, 2, 5]
def baseStart_778528 : Nat := 118140960795 + 778528 * 2 ^ 59
def prefixEnd_778528 : Nat := 4983230072969 + 3 ^ 40 * 778528 * 2
def baseEnd_778528 : Nat := 177670696437171217475387

theorem tailTrace_778528 : CollatzResearch.WordTrace tailWord_778528 prefixEnd_778528 177670696437171217475387 := by
  unfold tailWord_778528
  simp only [CollatzResearch.WordTrace]
  refine ⟨14197624461766746420932119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18930165949022328561242825 14197624461766746420932119)
  ·
    refine ⟨21296436692650119631398179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14197624461766746420932119 21296436692650119631398179)
    ·
      refine ⟨31944655038975179447097269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21296436692650119631398179 31944655038975179447097269)
      ·
        refine ⟨2994811409903923073165369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31944655038975179447097269 2994811409903923073165369)
        ·
          refine ⟨2246108557427942304874027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2994811409903923073165369 2246108557427942304874027)
          ·
            refine ⟨3369162836141913457311041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2246108557427942304874027 3369162836141913457311041)
            ·
              refine ⟨2526872127106435092983281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3369162836141913457311041 2526872127106435092983281)
              ·
                refine ⟨1895154095329826319737461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2526872127106435092983281 1895154095329826319737461)
                ·
                  refine ⟨177670696437171217475387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1895154095329826319737461 177670696437171217475387)
                  ·
                    rfl

theorem cell21_778528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 5].length) (baseStart_778528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_778528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_778528 prefixEnd_778528 := by exact prefixLift 778528
  have htrace : WordTrace (prefixWord ++ tailWord_778528) baseStart_778528 baseEnd_778528 := by
    simpa [prefixWord, tailWord_778528, baseEnd_778528] using wordTrace_append hprefix tailTrace_778528
  have hstable : (prefixWord ++ tailWord_778528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778528).length < 2 ^ (prefixWord ++ tailWord_778528).sum := by decide
  have hdescent : baseEnd_778528 < baseStart_778528 := by decide
  rcases family_descends (prefixWord ++ tailWord_778528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778576 : List Nat := [2, 1, 1, 1, 1, 8, 2, 1, 4]
def baseStart_778576 : Nat := 118140960795 + 778576 * 2 ^ 59
def prefixEnd_778576 : Nat := 4983230072969 + 3 ^ 40 * 778576 * 2
def baseEnd_778576 : Nat := 177681650691133800675289

theorem tailTrace_778576 : CollatzResearch.WordTrace tailWord_778576 prefixEnd_778576 177681650691133800675289 := by
  unfold tailWord_778576
  simp only [CollatzResearch.WordTrace]
  refine ⟨14198499813679798519805791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18931333084906398026407721 14198499813679798519805791)
  ·
    refine ⟨21297749720519697779708687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14198499813679798519805791 21297749720519697779708687)
    ·
      refine ⟨31946624580779546669563031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21297749720519697779708687 31946624580779546669563031)
      ·
        refine ⟨47919936871169320004344547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31946624580779546669563031 47919936871169320004344547)
        ·
          refine ⟨71879905306753980006516821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47919936871169320004344547 71879905306753980006516821)
          ·
            refine ⟨842342640313523203201369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 71879905306753980006516821 842342640313523203201369)
            ·
              refine ⟨631756980235142402401027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 842342640313523203201369 631756980235142402401027)
              ·
                refine ⟨947635470352713603601541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631756980235142402401027 947635470352713603601541)
                ·
                  refine ⟨177681650691133800675289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 947635470352713603601541 177681650691133800675289)
                  ·
                    rfl

theorem cell21_778576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 4].length) (baseStart_778576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_778576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_778576 prefixEnd_778576 := by exact prefixLift 778576
  have htrace : WordTrace (prefixWord ++ tailWord_778576) baseStart_778576 baseEnd_778576 := by
    simpa [prefixWord, tailWord_778576, baseEnd_778576] using wordTrace_append hprefix tailTrace_778576
  have hstable : (prefixWord ++ tailWord_778576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778576).length < 2 ^ (prefixWord ++ tailWord_778576).sum := by decide
  have hdescent : baseEnd_778576 < baseStart_778576 := by decide
  rcases family_descends (prefixWord ++ tailWord_778576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778621 : List Nat := [1, 4, 1, 1, 2, 4, 1, 4, 3]
def baseStart_778621 : Nat := 118140960795 + 778621 * 2 ^ 59
def prefixEnd_778621 : Nat := 4983230072969 + 3 ^ 40 * 778621 * 2
def baseEnd_778621 : Nat := 177691920304223722425197

theorem tailTrace_778621 : CollatzResearch.WordTrace tailWord_778621 prefixEnd_778621 177691920304223722425197 := by
  unfold tailWord_778621
  simp only [CollatzResearch.WordTrace]
  refine ⟨28398640912196569724999717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18932427274797713149999811 28398640912196569724999717)
  ·
    refine ⟨5324745171036856823437447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28398640912196569724999717 5324745171036856823437447)
    ·
      refine ⟨7987117756555285235156171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5324745171036856823437447 7987117756555285235156171)
      ·
        refine ⟨11980676634832927852734257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7987117756555285235156171 11980676634832927852734257)
        ·
          refine ⟨8985507476124695889550693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11980676634832927852734257 8985507476124695889550693)
          ·
            refine ⟨1684782651773380479290755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8985507476124695889550693 1684782651773380479290755)
            ·
              refine ⟨2527173977660070718936133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1684782651773380479290755 2527173977660070718936133)
              ·
                refine ⟨473845120811263259800525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2527173977660070718936133 473845120811263259800525)
                ·
                  refine ⟨177691920304223722425197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 473845120811263259800525 177691920304223722425197)
                  ·
                    rfl

theorem cell21_778621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_778621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_778621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_778621 prefixEnd_778621 := by exact prefixLift 778621
  have htrace : WordTrace (prefixWord ++ tailWord_778621) baseStart_778621 baseEnd_778621 := by
    simpa [prefixWord, tailWord_778621, baseEnd_778621] using wordTrace_append hprefix tailTrace_778621
  have hstable : (prefixWord ++ tailWord_778621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778621).length < 2 ^ (prefixWord ++ tailWord_778621).sum := by decide
  have hdescent : baseEnd_778621 < baseStart_778621 := by decide
  rcases family_descends (prefixWord ++ tailWord_778621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778649 : List Nat := [1, 2, 1, 2, 1, 4, 5, 5]
def baseStart_778649 : Nat := 118140960795 + 778649 * 2 ^ 59
def prefixEnd_778649 : Nat := 4983230072969 + 3 ^ 40 * 778649 * 2
def baseEnd_778649 : Nat := 59232770095233965319491

theorem tailTrace_778649 : CollatzResearch.WordTrace tailWord_778649 prefixEnd_778649 59232770095233965319491 := by
  unfold tailWord_778649
  simp only [CollatzResearch.WordTrace]
  refine ⟨28399662156095130507019001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18933108104063420338012667 28399662156095130507019001)
  ·
    refine ⟨21299746617071347880264251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28399662156095130507019001 21299746617071347880264251)
    ·
      refine ⟨31949619925607021820396377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21299746617071347880264251 31949619925607021820396377)
      ·
        refine ⟨23962214944205266365297283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31949619925607021820396377 23962214944205266365297283)
        ·
          refine ⟨35943322416307899547945925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23962214944205266365297283 35943322416307899547945925)
          ·
            refine ⟨6739372953057731165239861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35943322416307899547945925 6739372953057731165239861)
            ·
              refine ⟨631816214349162296741237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6739372953057731165239861 631816214349162296741237)
              ·
                refine ⟨59232770095233965319491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 631816214349162296741237 59232770095233965319491)
                ·
                  rfl

theorem cell21_778649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 5].length) (baseStart_778649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_778649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_778649 prefixEnd_778649 := by exact prefixLift 778649
  have htrace : WordTrace (prefixWord ++ tailWord_778649) baseStart_778649 baseEnd_778649 := by
    simpa [prefixWord, tailWord_778649, baseEnd_778649] using wordTrace_append hprefix tailTrace_778649
  have hstable : (prefixWord ++ tailWord_778649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778649).length < 2 ^ (prefixWord ++ tailWord_778649).sum := by decide
  have hdescent : baseEnd_778649 < baseStart_778649 := by decide
  rcases family_descends (prefixWord ++ tailWord_778649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778669 : List Nat := [1, 5, 2, 2, 2, 2, 1, 2, 4]
def baseStart_778669 : Nat := 118140960795 + 778669 * 2 ^ 59
def prefixEnd_778669 : Nat := 4983230072969 + 3 ^ 40 * 778669 * 2
def baseEnd_778669 : Nat := 177702874558186305625099

theorem tailTrace_778669 : CollatzResearch.WordTrace tailWord_778669 prefixEnd_778669 177702874558186305625099 := by
  unfold tailWord_778669
  simp only [CollatzResearch.WordTrace]
  refine ⟨28400391616022673922747061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18933594410681782615164707 28400391616022673922747061)
  ·
    refine ⟨2662536714002125680257537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28400391616022673922747061 2662536714002125680257537)
    ·
      refine ⟨1996902535501594260193153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2662536714002125680257537 1996902535501594260193153)
      ·
        refine ⟨1497676901626195695144865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1996902535501594260193153 1497676901626195695144865)
        ·
          refine ⟨1123257676219646771358649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1497676901626195695144865 1123257676219646771358649)
          ·
            refine ⟨842443257164735078518987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1123257676219646771358649 842443257164735078518987)
            ·
              refine ⟨1263664885747102617778481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 842443257164735078518987 1263664885747102617778481)
              ·
                refine ⟨947748664310326963333861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1263664885747102617778481 947748664310326963333861)
                ·
                  refine ⟨177702874558186305625099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 947748664310326963333861 177702874558186305625099)
                  ·
                    rfl

theorem cell21_778669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_778669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_778669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_778669 prefixEnd_778669 := by exact prefixLift 778669
  have htrace : WordTrace (prefixWord ++ tailWord_778669) baseStart_778669 baseEnd_778669 := by
    simpa [prefixWord, tailWord_778669, baseEnd_778669] using wordTrace_append hprefix tailTrace_778669
  have hstable : (prefixWord ++ tailWord_778669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778669).length < 2 ^ (prefixWord ++ tailWord_778669).sum := by decide
  have hdescent : baseEnd_778669 < baseStart_778669 := by decide
  rcases family_descends (prefixWord ++ tailWord_778669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778784 : List Nat := [2, 1, 1, 6, 11]
def baseStart_778784 : Nat := 118140960795 + 778784 * 2 ^ 59
def prefixEnd_778784 : Nat := 4983230072969 + 3 ^ 40 * 778784 * 2
def baseEnd_778784 : Nat := 2194186655863847669237

theorem tailTrace_778784 : CollatzResearch.WordTrace tailWord_778784 prefixEnd_778784 2194186655863847669237 := by
  unfold tailWord_778784
  simp only [CollatzResearch.WordTrace]
  refine ⟨14202293005303024281591703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18936390673737365708788937 14202293005303024281591703)
  ·
    refine ⟨21303439507954536422387555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14202293005303024281591703 21303439507954536422387555)
    ·
      refine ⟨31955159261931804633581333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21303439507954536422387555 31955159261931804633581333)
      ·
        refine ⟨1497898090403053342199125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31955159261931804633581333 1497898090403053342199125)
        ·
          refine ⟨2194186655863847669237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1497898090403053342199125 2194186655863847669237)
          ·
            rfl

theorem cell21_778784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 11].length) (baseStart_778784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_778784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_778784 prefixEnd_778784 := by exact prefixLift 778784
  have htrace : WordTrace (prefixWord ++ tailWord_778784) baseStart_778784 baseEnd_778784 := by
    simpa [prefixWord, tailWord_778784, baseEnd_778784] using wordTrace_append hprefix tailTrace_778784
  have hstable : (prefixWord ++ tailWord_778784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778784).length < 2 ^ (prefixWord ++ tailWord_778784).sum := by decide
  have hdescent : baseEnd_778784 < baseStart_778784 := by decide
  rcases family_descends (prefixWord ++ tailWord_778784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778787 : List Nat := [1, 1, 1, 4, 4, 2, 2, 2, 4]
def baseStart_778787 : Nat := 118140960795 + 778787 * 2 ^ 59
def prefixEnd_778787 : Nat := 4983230072969 + 3 ^ 40 * 778787 * 2
def baseEnd_778787 : Nat := 177729803765844322658191

theorem tailTrace_778787 : CollatzResearch.WordTrace tailWord_778787 prefixEnd_778787 177729803765844322658191 := by
  unfold tailWord_778787
  simp only [CollatzResearch.WordTrace]
  refine ⟨28404695429595180075542615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18936463619730120050361743 28404695429595180075542615)
  ·
    refine ⟨42607043144392770113313923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28404695429595180075542615 42607043144392770113313923)
    ·
      refine ⟨63910564716589155169970885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42607043144392770113313923 63910564716589155169970885)
      ·
        refine ⟨11983230884360466594369541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63910564716589155169970885 11983230884360466594369541)
        ·
          refine ⟨2246855790817587486444289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11983230884360466594369541 2246855790817587486444289)
          ·
            refine ⟨1685141843113190614833217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2246855790817587486444289 1685141843113190614833217)
            ·
              refine ⟨1263856382334892961124913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1685141843113190614833217 1263856382334892961124913)
              ·
                refine ⟨947892286751169720843685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1263856382334892961124913 947892286751169720843685)
                ·
                  refine ⟨177729803765844322658191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 947892286751169720843685 177729803765844322658191)
                  ·
                    rfl

theorem cell21_778787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 4].length) (baseStart_778787 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_778787 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_778787 prefixEnd_778787 := by exact prefixLift 778787
  have htrace : WordTrace (prefixWord ++ tailWord_778787) baseStart_778787 baseEnd_778787 := by
    simpa [prefixWord, tailWord_778787, baseEnd_778787] using wordTrace_append hprefix tailTrace_778787
  have hstable : (prefixWord ++ tailWord_778787).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778787).length < 2 ^ (prefixWord ++ tailWord_778787).sum := by decide
  have hdescent : baseEnd_778787 < baseStart_778787 := by decide
  rcases family_descends (prefixWord ++ tailWord_778787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778815 : List Nat := [1, 1, 2, 2, 3, 2, 3, 2, 5]
def baseStart_778815 : Nat := 118140960795 + 778815 * 2 ^ 59
def prefixEnd_778815 : Nat := 4983230072969 + 3 ^ 40 * 778815 * 2
def baseEnd_778815 : Nat := 177736193747322496191467

theorem tailTrace_778815 : CollatzResearch.WordTrace tailWord_778815 prefixEnd_778815 177736193747322496191467 := by
  unfold tailWord_778815
  simp only [CollatzResearch.WordTrace]
  refine ⟨28405716673493740857561899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18937144448995827238374599 28405716673493740857561899)
  ·
    refine ⟨42608575010240611286342849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28405716673493740857561899 42608575010240611286342849)
    ·
      refine ⟨31956431257680458464757137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42608575010240611286342849 31956431257680458464757137)
      ·
        refine ⟨23967323443260343848567853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31956431257680458464757137 23967323443260343848567853)
        ·
          refine ⟨8987746291222628943212945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23967323443260343848567853 8987746291222628943212945)
          ·
            refine ⟨6740809718416971707409709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8987746291222628943212945 6740809718416971707409709)
            ·
              refine ⟨2527803644406364390278641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6740809718416971707409709 2527803644406364390278641)
              ·
                refine ⟨1895852733304773292708981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2527803644406364390278641 1895852733304773292708981)
                ·
                  refine ⟨177736193747322496191467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1895852733304773292708981 177736193747322496191467)
                  ·
                    rfl

theorem cell21_778815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 5].length) (baseStart_778815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_778815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_778815 prefixEnd_778815 := by exact prefixLift 778815
  have htrace : WordTrace (prefixWord ++ tailWord_778815) baseStart_778815 baseEnd_778815 := by
    simpa [prefixWord, tailWord_778815, baseEnd_778815] using wordTrace_append hprefix tailTrace_778815
  have hstable : (prefixWord ++ tailWord_778815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778815).length < 2 ^ (prefixWord ++ tailWord_778815).sum := by decide
  have hdescent : baseEnd_778815 < baseStart_778815 := by decide
  rcases family_descends (prefixWord ++ tailWord_778815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778877 : List Nat := [1, 4, 1, 1, 5, 1, 1, 7]
def baseStart_778877 : Nat := 118140960795 + 778877 * 2 ^ 59
def prefixEnd_778877 : Nat := 4983230072969 + 3 ^ 40 * 778877 * 2
def baseEnd_778877 : Nat := 59250114330674722052669

theorem tailTrace_778877 : CollatzResearch.WordTrace tailWord_778877 prefixEnd_778877 59250114330674722052669 := by
  unfold tailWord_778877
  simp only [CollatzResearch.WordTrace]
  refine ⟨28407977999269125446318885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18938651999512750297545923 28407977999269125446318885)
  ·
    refine ⟨5326495874862961021184791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28407977999269125446318885 5326495874862961021184791)
    ·
      refine ⟨7989743812294441531777187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5326495874862961021184791 7989743812294441531777187)
      ·
        refine ⟨11984615718441662297665781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7989743812294441531777187 11984615718441662297665781)
        ·
          refine ⟨1123557723603905840406167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11984615718441662297665781 1123557723603905840406167)
          ·
            refine ⟨1685336585405858760609251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1123557723603905840406167 1685336585405858760609251)
            ·
              refine ⟨2528004878108788140913877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1685336585405858760609251 2528004878108788140913877)
              ·
                refine ⟨59250114330674722052669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2528004878108788140913877 59250114330674722052669)
                ·
                  rfl

theorem cell21_778877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 7].length) (baseStart_778877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_778877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_778877 prefixEnd_778877 := by exact prefixLift 778877
  have htrace : WordTrace (prefixWord ++ tailWord_778877) baseStart_778877 baseEnd_778877 := by
    simpa [prefixWord, tailWord_778877, baseEnd_778877] using wordTrace_append hprefix tailTrace_778877
  have hstable : (prefixWord ++ tailWord_778877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778877).length < 2 ^ (prefixWord ++ tailWord_778877).sum := by decide
  have hdescent : baseEnd_778877 < baseStart_778877 := by decide
  rcases family_descends (prefixWord ++ tailWord_778877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778905 : List Nat := [1, 2, 1, 2, 1, 2, 3, 3, 6]
def baseStart_778905 : Nat := 118140960795 + 778905 * 2 ^ 59
def prefixEnd_778905 : Nat := 4983230072969 + 3 ^ 40 * 778905 * 2
def baseEnd_778905 : Nat := 177756732973502339691283

theorem tailTrace_778905 : CollatzResearch.WordTrace tailWord_778905 prefixEnd_778905 177756732973502339691283 := by
  unfold tailWord_778905
  simp only [CollatzResearch.WordTrace]
  refine ⟨28408999243167686228338169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18939332828778457485558779 28408999243167686228338169)
  ·
    refine ⟨21306749432375764671253627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28408999243167686228338169 21306749432375764671253627)
    ·
      refine ⟨31960124148563647006880441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21306749432375764671253627 31960124148563647006880441)
      ·
        refine ⟨23970093111422735255160331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31960124148563647006880441 23970093111422735255160331)
        ·
          refine ⟨35955139667134102882740497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23970093111422735255160331 35955139667134102882740497)
          ·
            refine ⟨26966354750350577162055373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35955139667134102882740497 26966354750350577162055373)
            ·
              refine ⟨10112383031381466435770765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26966354750350577162055373 10112383031381466435770765)
              ·
                refine ⟨3792143636768049913414037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10112383031381466435770765 3792143636768049913414037)
                ·
                  refine ⟨177756732973502339691283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3792143636768049913414037 177756732973502339691283)
                  ·
                    rfl

theorem cell21_778905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 6].length) (baseStart_778905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_778905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_778905 prefixEnd_778905 := by exact prefixLift 778905
  have htrace : WordTrace (prefixWord ++ tailWord_778905) baseStart_778905 baseEnd_778905 := by
    simpa [prefixWord, tailWord_778905, baseEnd_778905] using wordTrace_append hprefix tailTrace_778905
  have hstable : (prefixWord ++ tailWord_778905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778905).length < 2 ^ (prefixWord ++ tailWord_778905).sum := by decide
  have hdescent : baseEnd_778905 < baseStart_778905 := by decide
  rcases family_descends (prefixWord ++ tailWord_778905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778908 : List Nat := [2, 2, 3, 2, 2, 1, 3, 1, 5]
def baseStart_778908 : Nat := 118140960795 + 778908 * 2 ^ 59
def prefixEnd_778908 : Nat := 4983230072969 + 3 ^ 40 * 778908 * 2
def baseEnd_778908 : Nat := 177757417614375001141277

theorem tailTrace_778908 : CollatzResearch.WordTrace tailWord_778908 prefixEnd_778908 177757417614375001141277 := by
  unfold tailWord_778908
  simp only [CollatzResearch.WordTrace]
  refine ⟨14204554331078408870348689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18939405774771211827131585 14204554331078408870348689)
  ·
    refine ⟨10653415748308806652761517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14204554331078408870348689 10653415748308806652761517)
    ·
      refine ⟨3995030905615802494785569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10653415748308806652761517 3995030905615802494785569)
      ·
        refine ⟨2996273179211851871089177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3995030905615802494785569 2996273179211851871089177)
        ·
          refine ⟨2247204884408888903316883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2996273179211851871089177 2247204884408888903316883)
          ·
            refine ⟨3370807326613333354975325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2247204884408888903316883 3370807326613333354975325)
            ·
              refine ⟨1264052747480000008115747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3370807326613333354975325 1264052747480000008115747)
              ·
                refine ⟨1896079121220000012173621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1264052747480000008115747 1896079121220000012173621)
                ·
                  refine ⟨177757417614375001141277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1896079121220000012173621 177757417614375001141277)
                  ·
                    rfl

theorem cell21_778908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_778908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_778908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_778908 prefixEnd_778908 := by exact prefixLift 778908
  have htrace : WordTrace (prefixWord ++ tailWord_778908) baseStart_778908 baseEnd_778908 := by
    simpa [prefixWord, tailWord_778908, baseEnd_778908] using wordTrace_append hprefix tailTrace_778908
  have hstable : (prefixWord ++ tailWord_778908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778908).length < 2 ^ (prefixWord ++ tailWord_778908).sum := by decide
  have hdescent : baseEnd_778908 < baseStart_778908 := by decide
  rcases family_descends (prefixWord ++ tailWord_778908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778984 : List Nat := [2, 1, 4, 1, 4, 1, 1, 2, 5]
def baseStart_778984 : Nat := 118140960795 + 778984 * 2 ^ 59
def prefixEnd_778984 : Nat := 4983230072969 + 3 ^ 40 * 778984 * 2
def baseEnd_778984 : Nat := 177774761849815757874455

theorem tailTrace_778984 : CollatzResearch.WordTrace tailWord_778984 prefixEnd_778984 177774761849815757874455 := by
  unfold tailWord_778984
  simp only [CollatzResearch.WordTrace]
  refine ⟨14205940304940741360232003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18941253739920988480309337 14205940304940741360232003)
  ·
    refine ⟨21308910457411112040348005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14205940304940741360232003 21308910457411112040348005)
    ·
      refine ⟨3995420710764583507565251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21308910457411112040348005 3995420710764583507565251)
      ·
        refine ⟨5993131066146875261347877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3995420710764583507565251 5993131066146875261347877)
        ·
          refine ⟨1123712074902539111502727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5993131066146875261347877 1123712074902539111502727)
          ·
            refine ⟨1685568112353808667254091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1123712074902539111502727 1685568112353808667254091)
            ·
              refine ⟨2528352168530713000881137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1685568112353808667254091 2528352168530713000881137)
              ·
                refine ⟨1896264126398034750660853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2528352168530713000881137 1896264126398034750660853)
                ·
                  refine ⟨177774761849815757874455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1896264126398034750660853 177774761849815757874455)
                  ·
                    rfl

theorem cell21_778984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 5].length) (baseStart_778984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_778984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_778984 prefixEnd_778984 := by exact prefixLift 778984
  have htrace : WordTrace (prefixWord ++ tailWord_778984) baseStart_778984 baseEnd_778984 := by
    simpa [prefixWord, tailWord_778984, baseEnd_778984] using wordTrace_append hprefix tailTrace_778984
  have hstable : (prefixWord ++ tailWord_778984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778984).length < 2 ^ (prefixWord ++ tailWord_778984).sum := by decide
  have hdescent : baseEnd_778984 < baseStart_778984 := by decide
  rcases family_descends (prefixWord ++ tailWord_778984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778998 : List Nat := [5, 1, 1, 1, 1, 2, 2, 2, 6]
def baseStart_778998 : Nat := 118140960795 + 778998 * 2 ^ 59
def prefixEnd_778998 : Nat := 4983230072969 + 3 ^ 40 * 778998 * 2
def baseEnd_778998 : Nat := 177777956840554844641093

theorem tailTrace_778998 : CollatzResearch.WordTrace tailWord_778998 prefixEnd_778998 177777956840554844641093 := by
  unfold tailWord_778998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1775774451989422694467103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18941594154553842074315765 1775774451989422694467103)
  ·
    refine ⟨2663661677984134041700655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1775774451989422694467103 2663661677984134041700655)
    ·
      refine ⟨3995492516976201062550983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2663661677984134041700655 3995492516976201062550983)
      ·
        refine ⟨5993238775464301593826475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3995492516976201062550983 5993238775464301593826475)
        ·
          refine ⟨8989858163196452390739713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5993238775464301593826475 8989858163196452390739713)
          ·
            refine ⟨6742393622397339293054785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8989858163196452390739713 6742393622397339293054785)
            ·
              refine ⟨5056795216798004469791089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6742393622397339293054785 5056795216798004469791089)
              ·
                refine ⟨3792596412598503352343317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5056795216798004469791089 3792596412598503352343317)
                ·
                  refine ⟨177777956840554844641093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3792596412598503352343317 177777956840554844641093)
                  ·
                    rfl

theorem cell21_778998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_778998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_778998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_778998 prefixEnd_778998 := by exact prefixLift 778998
  have htrace : WordTrace (prefixWord ++ tailWord_778998) baseStart_778998 baseEnd_778998 := by
    simpa [prefixWord, tailWord_778998, baseEnd_778998] using wordTrace_append hprefix tailTrace_778998
  have hstable : (prefixWord ++ tailWord_778998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778998).length < 2 ^ (prefixWord ++ tailWord_778998).sum := by decide
  have hdescent : baseEnd_778998 < baseStart_778998 := by decide
  rcases family_descends (prefixWord ++ tailWord_778998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779012 : List Nat := [2, 3, 2, 2, 1, 1, 10]
def baseStart_779012 : Nat := 118140960795 + 779012 * 2 ^ 59
def prefixEnd_779012 : Nat := 4983230072969 + 3 ^ 40 * 779012 * 2
def baseEnd_779012 : Nat := 19753461314588214600859

theorem tailTrace_779012 : CollatzResearch.WordTrace tailWord_779012 prefixEnd_779012 19753461314588214600859 := by
  unfold tailWord_779012
  simp only [CollatzResearch.WordTrace]
  refine ⟨14206450926890021751241645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18941934569186695668322193 14206450926890021751241645)
  ·
    refine ⟨5327419097583758156715617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14206450926890021751241645 5327419097583758156715617)
    ·
      refine ⟨3995564323187818617536713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5327419097583758156715617 3995564323187818617536713)
      ·
        refine ⟨2996673242390863963152535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3995564323187818617536713 2996673242390863963152535)
        ·
          refine ⟨4495009863586295944728803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2996673242390863963152535 4495009863586295944728803)
          ·
            refine ⟨6742514795379443917093205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4495009863586295944728803 6742514795379443917093205)
            ·
              refine ⟨19753461314588214600859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6742514795379443917093205 19753461314588214600859)
              ·
                rfl

theorem cell21_779012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 10].length) (baseStart_779012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_779012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_779012 prefixEnd_779012 := by exact prefixLift 779012
  have htrace : WordTrace (prefixWord ++ tailWord_779012) baseStart_779012 baseEnd_779012 := by
    simpa [prefixWord, tailWord_779012, baseEnd_779012] using wordTrace_append hprefix tailTrace_779012
  have hstable : (prefixWord ++ tailWord_779012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779012).length < 2 ^ (prefixWord ++ tailWord_779012).sum := by decide
  have hdescent : baseEnd_779012 < baseStart_779012 := by decide
  rcases family_descends (prefixWord ++ tailWord_779012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779015 : List Nat := [1, 1, 4, 4, 1, 1, 3, 2, 4]
def baseStart_779015 : Nat := 118140960795 + 779015 * 2 ^ 59
def prefixEnd_779015 : Nat := 4983230072969 + 3 ^ 40 * 779015 * 2
def baseEnd_779015 : Nat := 177781836472166592857725

theorem tailTrace_779015 : CollatzResearch.WordTrace tailWord_779015 prefixEnd_779015 177781836472166592857725 := by
  unfold tailWord_779015
  simp only [CollatzResearch.WordTrace]
  refine ⟨28413011272769175014842499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18942007515179450009894999 28413011272769175014842499)
  ·
    refine ⟨42619516909153762522263749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28413011272769175014842499 42619516909153762522263749)
    ·
      refine ⟨7991159420466330472924453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42619516909153762522263749 7991159420466330472924453)
      ·
        refine ⟨1498342391337436963673335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7991159420466330472924453 1498342391337436963673335)
        ·
          refine ⟨2247513587006155445510003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1498342391337436963673335 2247513587006155445510003)
          ·
            refine ⟨3371270380509233168265005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2247513587006155445510003 3371270380509233168265005)
            ·
              refine ⟨1264226392690962438099377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3371270380509233168265005 1264226392690962438099377)
              ·
                refine ⟨948169794518221828574533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1264226392690962438099377 948169794518221828574533)
                ·
                  refine ⟨177781836472166592857725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 948169794518221828574533 177781836472166592857725)
                  ·
                    rfl

theorem cell21_779015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 4].length) (baseStart_779015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_779015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_779015 prefixEnd_779015 := by exact prefixLift 779015
  have htrace : WordTrace (prefixWord ++ tailWord_779015) baseStart_779015 baseEnd_779015 := by
    simpa [prefixWord, tailWord_779015, baseEnd_779015] using wordTrace_append hprefix tailTrace_779015
  have hstable : (prefixWord ++ tailWord_779015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779015).length < 2 ^ (prefixWord ++ tailWord_779015).sum := by decide
  have hdescent : baseEnd_779015 < baseStart_779015 := by decide
  rcases family_descends (prefixWord ++ tailWord_779015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779057 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 8]
def baseStart_779057 : Nat := 118140960795 + 779057 * 2 ^ 59
def prefixEnd_779057 : Nat := 4983230072969 + 3 ^ 40 * 779057 * 2
def baseEnd_779057 : Nat := 177791421444383853157639

theorem tailTrace_779057 : CollatzResearch.WordTrace tailWord_779057 prefixEnd_779057 177791421444383853157639 := by
  unfold tailWord_779057
  simp only [CollatzResearch.WordTrace]
  refine ⟨28414543138617016187871425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18943028759078010791914283 28414543138617016187871425)
  ·
    refine ⟨21310907353962762140903569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28414543138617016187871425 21310907353962762140903569)
    ·
      refine ⟨15983180515472071605677677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21310907353962762140903569 15983180515472071605677677)
      ·
        refine ⟨5993692693302026852129129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15983180515472071605677677 5993692693302026852129129)
        ·
          refine ⟨4495269519976520139096847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5993692693302026852129129 4495269519976520139096847)
          ·
            refine ⟨6742904279964780208645271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4495269519976520139096847 6742904279964780208645271)
            ·
              refine ⟨10114356419947170312967907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6742904279964780208645271 10114356419947170312967907)
              ·
                refine ⟨15171534629920755469451861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10114356419947170312967907 15171534629920755469451861)
                ·
                  refine ⟨177791421444383853157639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15171534629920755469451861 177791421444383853157639)
                  ·
                    rfl

theorem cell21_779057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 8].length) (baseStart_779057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_779057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_779057 prefixEnd_779057 := by exact prefixLift 779057
  have htrace : WordTrace (prefixWord ++ tailWord_779057) baseStart_779057 baseEnd_779057 := by
    simpa [prefixWord, tailWord_779057, baseEnd_779057] using wordTrace_append hprefix tailTrace_779057
  have hstable : (prefixWord ++ tailWord_779057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779057).length < 2 ^ (prefixWord ++ tailWord_779057).sum := by decide
  have hdescent : baseEnd_779057 < baseStart_779057 := by decide
  rcases family_descends (prefixWord ++ tailWord_779057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779133 : List Nat := [1, 4, 1, 1, 2, 1, 2, 3, 6]
def baseStart_779133 : Nat := 118140960795 + 779133 * 2 ^ 59
def prefixEnd_779133 : Nat := 4983230072969 + 3 ^ 40 * 779133 * 2
def baseEnd_779133 : Nat := 177808765679824609890817

theorem tailTrace_779133 : CollatzResearch.WordTrace tailWord_779133 prefixEnd_779133 177808765679824609890817 := by
  unfold tailWord_779133
  simp only [CollatzResearch.WordTrace]
  refine ⟨28417315086341681167638053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18944876724227787445092035 28417315086341681167638053)
  ·
    refine ⟨5328246578689065218932135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28417315086341681167638053 5328246578689065218932135)
    ·
      refine ⟨7992369868033597828398203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5328246578689065218932135 7992369868033597828398203)
      ·
        refine ⟨11988554802050396742597305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7992369868033597828398203 11988554802050396742597305)
        ·
          refine ⟨8991416101537797556947979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11988554802050396742597305 8991416101537797556947979)
          ·
            refine ⟨13487124152306696335421969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8991416101537797556947979 13487124152306696335421969)
            ·
              refine ⟨10115343114230022251566477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13487124152306696335421969 10115343114230022251566477)
              ·
                refine ⟨3793253667836258344337429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10115343114230022251566477 3793253667836258344337429)
                ·
                  refine ⟨177808765679824609890817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3793253667836258344337429 177808765679824609890817)
                  ·
                    rfl

theorem cell21_779133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_779133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_779133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_779133 prefixEnd_779133 := by exact prefixLift 779133
  have htrace : WordTrace (prefixWord ++ tailWord_779133) baseStart_779133 baseEnd_779133 := by
    simpa [prefixWord, tailWord_779133, baseEnd_779133] using wordTrace_append hprefix tailTrace_779133
  have hstable : (prefixWord ++ tailWord_779133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779133).length < 2 ^ (prefixWord ++ tailWord_779133).sum := by decide
  have hdescent : baseEnd_779133 < baseStart_779133 := by decide
  rcases family_descends (prefixWord ++ tailWord_779133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779229 : List Nat := [1, 4, 3, 1, 2, 1, 3, 3, 3]
def baseStart_779229 : Nat := 118140960795 + 779229 * 2 ^ 59
def prefixEnd_779229 : Nat := 4983230072969 + 3 ^ 40 * 779229 * 2
def baseEnd_779229 : Nat := 177830674187749776290621

theorem tailTrace_779229 : CollatzResearch.WordTrace tailWord_779229 prefixEnd_779229 177830674187749776290621 := by
  unfold tailWord_779229
  simp only [CollatzResearch.WordTrace]
  refine ⟨28420816493993889563132741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18947210995995926375421827 28420816493993889563132741)
  ·
    refine ⟨5328903092623854293087389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28420816493993889563132741 5328903092623854293087389)
    ·
      refine ⟨1998338659733945359907771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5328903092623854293087389 1998338659733945359907771)
      ·
        refine ⟨2997507989600918039861657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1998338659733945359907771 2997507989600918039861657)
        ·
          refine ⟨2248130992200688529896243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2997507989600918039861657 2248130992200688529896243)
          ·
            refine ⟨3372196488301032794844365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2248130992200688529896243 3372196488301032794844365)
            ·
              refine ⟨1264573683112887298066637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3372196488301032794844365 1264573683112887298066637)
              ·
                refine ⟨474215131167332736774989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1264573683112887298066637 474215131167332736774989)
                ·
                  refine ⟨177830674187749776290621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 474215131167332736774989 177830674187749776290621)
                  ·
                    rfl

theorem cell21_779229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_779229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_779229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_779229 prefixEnd_779229 := by exact prefixLift 779229
  have htrace : WordTrace (prefixWord ++ tailWord_779229) baseStart_779229 baseEnd_779229 := by
    simpa [prefixWord, tailWord_779229, baseEnd_779229] using wordTrace_append hprefix tailTrace_779229
  have hstable : (prefixWord ++ tailWord_779229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779229).length < 2 ^ (prefixWord ++ tailWord_779229).sum := by decide
  have hdescent : baseEnd_779229 < baseStart_779229 := by decide
  rcases family_descends (prefixWord ++ tailWord_779229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779246 : List Nat := [4, 1, 2, 1, 4, 1, 3, 2, 3]
def baseStart_779246 : Nat := 118140960795 + 779246 * 2 ^ 59
def prefixEnd_779246 : Nat := 4983230072969 + 3 ^ 40 * 779246 * 2
def baseEnd_779246 : Nat := 177834553819361524507253

theorem tailTrace_779246 : CollatzResearch.WordTrace tailWord_779246 prefixEnd_779246 177834553819361524507253 := by
  unfold tailWord_779246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3552679566866537683312699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18947624356621534311001061 3552679566866537683312699)
  ·
    refine ⟨5329019350299806524969049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3552679566866537683312699 5329019350299806524969049)
    ·
      refine ⟨3996764512724854893726787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5329019350299806524969049 3996764512724854893726787)
      ·
        refine ⟨5995146769087282340590181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3996764512724854893726787 5995146769087282340590181)
        ·
          refine ⟨1124090019203865438860659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5995146769087282340590181 1124090019203865438860659)
          ·
            refine ⟨1686135028805798158290989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1124090019203865438860659 1686135028805798158290989)
            ·
              refine ⟨632300635802174309359121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1686135028805798158290989 632300635802174309359121)
              ·
                refine ⟨474225476851630732019341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 632300635802174309359121 474225476851630732019341)
                ·
                  refine ⟨177834553819361524507253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 474225476851630732019341 177834553819361524507253)
                  ·
                    rfl

theorem cell21_779246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_779246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_779246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_779246 prefixEnd_779246 := by exact prefixLift 779246
  have htrace : WordTrace (prefixWord ++ tailWord_779246) baseStart_779246 baseEnd_779246 := by
    simpa [prefixWord, tailWord_779246, baseEnd_779246] using wordTrace_append hprefix tailTrace_779246
  have hstable : (prefixWord ++ tailWord_779246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779246).length < 2 ^ (prefixWord ++ tailWord_779246).sum := by decide
  have hdescent : baseEnd_779246 < baseStart_779246 := by decide
  rcases family_descends (prefixWord ++ tailWord_779246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779252 : List Nat := [2, 6, 2, 1, 2, 1, 2, 1, 4]
def baseStart_779252 : Nat := 118140960795 + 779252 * 2 ^ 59
def prefixEnd_779252 : Nat := 4983230072969 + 3 ^ 40 * 779252 * 2
def baseEnd_779252 : Nat := 177835923101106847407241

theorem tailTrace_779252 : CollatzResearch.WordTrace tailWord_779252 prefixEnd_779252 177835923101106847407241 := by
  unfold tailWord_779252
  simp only [CollatzResearch.WordTrace]
  refine ⟨14210827686455282245610005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18947770248607042994146673 14210827686455282245610005)
  ·
    refine ⟨666132547802591355262969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14210827686455282245610005 666132547802591355262969)
    ·
      refine ⟨499599410851943516447227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 666132547802591355262969 499599410851943516447227)
      ·
        refine ⟨749399116277915274670841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499599410851943516447227 749399116277915274670841)
        ·
          refine ⟨562049337208436456003131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 749399116277915274670841 562049337208436456003131)
          ·
            refine ⟨843074005812654684004697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562049337208436456003131 843074005812654684004697)
            ·
              refine ⟨632305504359491013003523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 843074005812654684004697 632305504359491013003523)
              ·
                refine ⟨948458256539236519505285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 632305504359491013003523 948458256539236519505285)
                ·
                  refine ⟨177835923101106847407241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 948458256539236519505285 177835923101106847407241)
                  ·
                    rfl

theorem cell21_779252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_779252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_779252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_779252 prefixEnd_779252 := by exact prefixLift 779252
  have htrace : WordTrace (prefixWord ++ tailWord_779252) baseStart_779252 baseEnd_779252 := by
    simpa [prefixWord, tailWord_779252, baseEnd_779252] using wordTrace_append hprefix tailTrace_779252
  have hstable : (prefixWord ++ tailWord_779252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779252).length < 2 ^ (prefixWord ++ tailWord_779252).sum := by decide
  have hdescent : baseEnd_779252 < baseStart_779252 := by decide
  rcases family_descends (prefixWord ++ tailWord_779252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779299 : List Nat := [1, 1, 1, 4, 3, 11]
def baseStart_779299 : Nat := 118140960795 + 779299 * 2 ^ 59
def prefixEnd_779299 : Nat := 4983230072969 + 3 ^ 40 * 779299 * 2
def baseEnd_779299 : Nat := 6586912931164637411993

theorem tailTrace_779299 : CollatzResearch.WordTrace tailWord_779299 prefixEnd_779299 6586912931164637411993 := by
  unfold tailWord_779299
  simp only [CollatzResearch.WordTrace]
  refine ⟨28423369603740291518180951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18948913069160194345453967 28423369603740291518180951)
  ·
    refine ⟨42635054405610437277271427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28423369603740291518180951 42635054405610437277271427)
    ·
      refine ⟨63952581608415655915907141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42635054405610437277271427 63952581608415655915907141)
      ·
        refine ⟨11991109051577935484232589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63952581608415655915907141 11991109051577935484232589)
        ·
          refine ⟨4496665894341725806587221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11991109051577935484232589 4496665894341725806587221)
          ·
            refine ⟨6586912931164637411993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4496665894341725806587221 6586912931164637411993)
            ·
              rfl

theorem cell21_779299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 11].length) (baseStart_779299 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_779299 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_779299 prefixEnd_779299 := by exact prefixLift 779299
  have htrace : WordTrace (prefixWord ++ tailWord_779299) baseStart_779299 baseEnd_779299 := by
    simpa [prefixWord, tailWord_779299, baseEnd_779299] using wordTrace_append hprefix tailTrace_779299
  have hstable : (prefixWord ++ tailWord_779299).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779299).length < 2 ^ (prefixWord ++ tailWord_779299).sum := by decide
  have hdescent : baseEnd_779299 < baseStart_779299 := by decide
  rcases family_descends (prefixWord ++ tailWord_779299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779347 : List Nat := [1, 1, 1, 2, 1, 1, 2, 9, 3]
def baseStart_779347 : Nat := 118140960795 + 779347 * 2 ^ 59
def prefixEnd_779347 : Nat := 4983230072969 + 3 ^ 40 * 779347 * 2
def baseEnd_779347 : Nat := 177857603395407793323713

theorem tailTrace_779347 : CollatzResearch.WordTrace tailWord_779347 prefixEnd_779347 177857603395407793323713 := by
  unfold tailWord_779347
  simp only [CollatzResearch.WordTrace]
  refine ⟨28425120307566395715928295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18950080205044263810618863 28425120307566395715928295)
  ·
    refine ⟨42637680461349593573892443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28425120307566395715928295 42637680461349593573892443)
    ·
      refine ⟨63956520692024390360838665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42637680461349593573892443 63956520692024390360838665)
      ·
        refine ⟨47967390519018292770628999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63956520692024390360838665 47967390519018292770628999)
        ·
          refine ⟨71951085778527439155943499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47967390519018292770628999 71951085778527439155943499)
          ·
            refine ⟨107926628667791158733915249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71951085778527439155943499 107926628667791158733915249)
            ·
              refine ⟨80944971500843369050436437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107926628667791158733915249 80944971500843369050436437)
              ·
                refine ⟨474286942387754115529901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 80944971500843369050436437 474286942387754115529901)
                ·
                  refine ⟨177857603395407793323713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 474286942387754115529901 177857603395407793323713)
                  ·
                    rfl

theorem cell21_779347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 9, 3].length) (baseStart_779347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_779347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_779347 prefixEnd_779347 := by exact prefixLift 779347
  have htrace : WordTrace (prefixWord ++ tailWord_779347) baseStart_779347 baseEnd_779347 := by
    simpa [prefixWord, tailWord_779347, baseEnd_779347] using wordTrace_append hprefix tailTrace_779347
  have hstable : (prefixWord ++ tailWord_779347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779347).length < 2 ^ (prefixWord ++ tailWord_779347).sum := by decide
  have hdescent : baseEnd_779347 < baseStart_779347 := by decide
  rcases family_descends (prefixWord ++ tailWord_779347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779350 : List Nat := [5, 2, 2, 1, 2, 1, 8]
def baseStart_779350 : Nat := 118140960795 + 779350 * 2 ^ 59
def prefixEnd_779350 : Nat := 4983230072969 + 3 ^ 40 * 779350 * 2
def baseEnd_779350 : Nat := 19762032004031161641523

theorem tailTrace_779350 : CollatzResearch.WordTrace tailWord_779350 prefixEnd_779350 19762032004031161641523 := by
  unfold tailWord_779350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1776576857909720451767969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18950153151037018152191669 1776576857909720451767969)
  ·
    refine ⟨1332432643432290338825977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1776576857909720451767969 1332432643432290338825977)
    ·
      refine ⟨999324482574217754119483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1332432643432290338825977 999324482574217754119483)
      ·
        refine ⟨1498986723861326631179225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 999324482574217754119483 1498986723861326631179225)
        ·
          refine ⟨1124240042895994973384419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1498986723861326631179225 1124240042895994973384419)
          ·
            refine ⟨1686360064343992460076629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1124240042895994973384419 1686360064343992460076629)
            ·
              refine ⟨19762032004031161641523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1686360064343992460076629 19762032004031161641523)
              ·
                rfl

theorem cell21_779350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 8].length) (baseStart_779350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_779350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_779350 prefixEnd_779350 := by exact prefixLift 779350
  have htrace : WordTrace (prefixWord ++ tailWord_779350) baseStart_779350 baseEnd_779350 := by
    simpa [prefixWord, tailWord_779350, baseEnd_779350] using wordTrace_append hprefix tailTrace_779350
  have hstable : (prefixWord ++ tailWord_779350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779350).length < 2 ^ (prefixWord ++ tailWord_779350).sum := by decide
  have hdescent : baseEnd_779350 < baseStart_779350 := by decide
  rcases family_descends (prefixWord ++ tailWord_779350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779375 : List Nat := [1, 1, 2, 1, 3, 3, 2, 8]
def baseStart_779375 : Nat := 118140960795 + 779375 * 2 ^ 59
def prefixEnd_779375 : Nat := 4983230072969 + 3 ^ 40 * 779375 * 2
def baseEnd_779375 : Nat := 59287997792295322285663

theorem tailTrace_779375 : CollatzResearch.WordTrace tailWord_779375 prefixEnd_779375 59287997792295322285663 := by
  unfold tailWord_779375
  simp only [CollatzResearch.WordTrace]
  refine ⟨28426141551464956497947579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18950761034309970998631719 28426141551464956497947579)
  ·
    refine ⟨42639212327197434746921369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28426141551464956497947579 42639212327197434746921369)
    ·
      refine ⟨31979409245398076060191027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42639212327197434746921369 31979409245398076060191027)
      ·
        refine ⟨47969113868097114090286541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31979409245398076060191027 47969113868097114090286541)
        ·
          refine ⟨17988417700536417783857453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47969113868097114090286541 17988417700536417783857453)
          ·
            refine ⟨6745656637701156668946545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17988417700536417783857453 6745656637701156668946545)
            ·
              refine ⟨5059242478275867501709909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6745656637701156668946545 5059242478275867501709909)
              ·
                refine ⟨59287997792295322285663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5059242478275867501709909 59287997792295322285663)
                ·
                  rfl

theorem cell21_779375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 8].length) (baseStart_779375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_779375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_779375 prefixEnd_779375 := by exact prefixLift 779375
  have htrace : WordTrace (prefixWord ++ tailWord_779375) baseStart_779375 baseEnd_779375 := by
    simpa [prefixWord, tailWord_779375, baseEnd_779375] using wordTrace_append hprefix tailTrace_779375
  have hstable : (prefixWord ++ tailWord_779375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779375).length < 2 ^ (prefixWord ++ tailWord_779375).sum := by decide
  have hdescent : baseEnd_779375 < baseStart_779375 := by decide
  rcases family_descends (prefixWord ++ tailWord_779375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779392 : List Nat := [2, 1, 1, 2, 1, 3, 6, 5]
def baseStart_779392 : Nat := 118140960795 + 779392 * 2 ^ 59
def prefixEnd_779392 : Nat := 4983230072969 + 3 ^ 40 * 779392 * 2
def baseEnd_779392 : Nat := 59289291002832571691207

theorem tailTrace_779392 : CollatzResearch.WordTrace tailWord_779392 prefixEnd_779392 59289291002832571691207 := by
  unfold tailWord_779392
  simp only [CollatzResearch.WordTrace]
  refine ⟨14213380796201684200658215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18951174394935578934210953 14213380796201684200658215)
  ·
    refine ⟨21320071194302526300987323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14213380796201684200658215 21320071194302526300987323)
    ·
      refine ⟨31980106791453789451480985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21320071194302526300987323 31980106791453789451480985)
      ·
        refine ⟨23985080093590342088610739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31980106791453789451480985 23985080093590342088610739)
        ·
          refine ⟨35977620140385513132916109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23985080093590342088610739 35977620140385513132916109)
          ·
            refine ⟨13491607552644567424843541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35977620140385513132916109 13491607552644567424843541)
            ·
              refine ⟨632419104030214098039541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13491607552644567424843541 632419104030214098039541)
              ·
                refine ⟨59289291002832571691207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 632419104030214098039541 59289291002832571691207)
                ·
                  rfl

theorem cell21_779392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 5].length) (baseStart_779392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_779392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_779392 prefixEnd_779392 := by exact prefixLift 779392
  have htrace : WordTrace (prefixWord ++ tailWord_779392) baseStart_779392 baseEnd_779392 := by
    simpa [prefixWord, tailWord_779392, baseEnd_779392] using wordTrace_append hprefix tailTrace_779392
  have hstable : (prefixWord ++ tailWord_779392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779392).length < 2 ^ (prefixWord ++ tailWord_779392).sum := by decide
  have hdescent : baseEnd_779392 < baseStart_779392 := by decide
  rcases family_descends (prefixWord ++ tailWord_779392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779482 : List Nat := [3, 1, 1, 2, 2, 1, 1, 5, 5]
def baseStart_779482 : Nat := 118140960795 + 779482 * 2 ^ 59
def prefixEnd_779482 : Nat := 4983230072969 + 3 ^ 40 * 779482 * 2
def baseEnd_779482 : Nat := 177888412234677558573437

theorem tailTrace_779482 : CollatzResearch.WordTrace tailWord_779482 prefixEnd_779482 177888412234677558573437 := by
  unfold tailWord_779482
  simp only [CollatzResearch.WordTrace]
  refine ⟨7107511040519328443023175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18953362774718209181395133 7107511040519328443023175)
  ·
    refine ⟨10661266560778992664534763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7107511040519328443023175 10661266560778992664534763)
    ·
      refine ⟨15991899841168488996802145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10661266560778992664534763 15991899841168488996802145)
      ·
        refine ⟨11993924880876366747601609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15991899841168488996802145 11993924880876366747601609)
        ·
          refine ⟨8995443660657275060701207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11993924880876366747601609 8995443660657275060701207)
          ·
            refine ⟨13493165490985912591051811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8995443660657275060701207 13493165490985912591051811)
            ·
              refine ⟨20239748236478868886577717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13493165490985912591051811 20239748236478868886577717)
              ·
                refine ⟨1897476397169893958116661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20239748236478868886577717 1897476397169893958116661)
                ·
                  refine ⟨177888412234677558573437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1897476397169893958116661 177888412234677558573437)
                  ·
                    rfl

theorem cell21_779482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_779482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_779482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_779482 prefixEnd_779482 := by exact prefixLift 779482
  have htrace : WordTrace (prefixWord ++ tailWord_779482) baseStart_779482 baseEnd_779482 := by
    simpa [prefixWord, tailWord_779482, baseEnd_779482] using wordTrace_append hprefix tailTrace_779482
  have hstable : (prefixWord ++ tailWord_779482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779482).length < 2 ^ (prefixWord ++ tailWord_779482).sum := by decide
  have hdescent : baseEnd_779482 < baseStart_779482 := by decide
  rcases family_descends (prefixWord ++ tailWord_779482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779603 : List Nat := [1, 1, 1, 2, 1, 1, 8, 6]
def baseStart_779603 : Nat := 118140960795 + 779603 * 2 ^ 59
def prefixEnd_779603 : Nat := 4983230072969 + 3 ^ 40 * 779603 * 2
def baseEnd_779603 : Nat := 59305342027736079018841

theorem tailTrace_779603 : CollatzResearch.WordTrace tailWord_779603 prefixEnd_779603 59305342027736079018841 := by
  unfold tailWord_779603
  simp only [CollatzResearch.WordTrace]
  refine ⟨28434457394638951437247463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18956304929759300958164975 28434457394638951437247463)
  ·
    refine ⟨42651686091958427155871195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28434457394638951437247463 42651686091958427155871195)
    ·
      refine ⟨63977529137937640733806793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42651686091958427155871195 63977529137937640733806793)
      ·
        refine ⟨47983146853453230550355095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63977529137937640733806793 47983146853453230550355095)
        ·
          refine ⟨71974720280179845825532643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47983146853453230550355095 71974720280179845825532643)
          ·
            refine ⟨107962080420269768738298965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71974720280179845825532643 107962080420269768738298965)
            ·
              refine ⟨1265180629925036352401941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 107962080420269768738298965 1265180629925036352401941)
              ·
                refine ⟨59305342027736079018841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1265180629925036352401941 59305342027736079018841)
                ·
                  rfl

theorem cell21_779603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 6].length) (baseStart_779603 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_779603 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_779603 prefixEnd_779603 := by exact prefixLift 779603
  have htrace : WordTrace (prefixWord ++ tailWord_779603) baseStart_779603 baseEnd_779603 := by
    simpa [prefixWord, tailWord_779603, baseEnd_779603] using wordTrace_append hprefix tailTrace_779603
  have hstable : (prefixWord ++ tailWord_779603).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779603).length < 2 ^ (prefixWord ++ tailWord_779603).sum := by decide
  have hdescent : baseEnd_779603 < baseStart_779603 := by decide
  rcases family_descends (prefixWord ++ tailWord_779603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779648 : List Nat := [2, 1, 1, 2, 1, 2, 1, 5, 6]
def baseStart_779648 : Nat := 118140960795 + 779648 * 2 ^ 59
def prefixEnd_779648 : Nat := 4983230072969 + 3 ^ 40 * 779648 * 2
def baseEnd_779648 : Nat := 177926295696298158806431

theorem tailTrace_779648 : CollatzResearch.WordTrace tailWord_779648 prefixEnd_779648 177926295696298158806431 := by
  unfold tailWord_779648
  simp only [CollatzResearch.WordTrace]
  refine ⟨14218049339737962061317799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18957399119650616081757065 14218049339737962061317799)
  ·
    refine ⟨21327074009606943091976699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14218049339737962061317799 21327074009606943091976699)
    ·
      refine ⟨31990611014410414637965049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21327074009606943091976699 31990611014410414637965049)
      ·
        refine ⟨23992958260807810978473787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31990611014410414637965049 23992958260807810978473787)
        ·
          refine ⟨35989437391211716467710681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23992958260807810978473787 35989437391211716467710681)
          ·
            refine ⟨26992078043408787350783011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35989437391211716467710681 26992078043408787350783011)
            ·
              refine ⟨40488117065113181026174517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26992078043408787350783011 40488117065113181026174517)
              ·
                refine ⟨3795760974854360721203861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40488117065113181026174517 3795760974854360721203861)
                ·
                  refine ⟨177926295696298158806431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3795760974854360721203861 177926295696298158806431)
                  ·
                    rfl

theorem cell21_779648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 6].length) (baseStart_779648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_779648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_779648 prefixEnd_779648 := by exact prefixLift 779648
  have htrace : WordTrace (prefixWord ++ tailWord_779648) baseStart_779648 baseEnd_779648 := by
    simpa [prefixWord, tailWord_779648, baseEnd_779648] using wordTrace_append hprefix tailTrace_779648
  have hstable : (prefixWord ++ tailWord_779648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779648).length < 2 ^ (prefixWord ++ tailWord_779648).sum := by decide
  have hdescent : baseEnd_779648 < baseStart_779648 := by decide
  rcases family_descends (prefixWord ++ tailWord_779648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779741 : List Nat := [1, 4, 3, 1, 1, 2, 1, 2, 6]
def baseStart_779741 : Nat := 118140960795 + 779741 * 2 ^ 59
def prefixEnd_779741 : Nat := 4983230072969 + 3 ^ 40 * 779741 * 2
def baseEnd_779741 : Nat := 177947519563350663756241

theorem tailTrace_779741 : CollatzResearch.WordTrace tailWord_779741 prefixEnd_779741 177947519563350663756241 := by
  unfold tailWord_779741
  simp only [CollatzResearch.WordTrace]
  refine ⟨28439490668139001005771077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18959660445426000670514051 28439490668139001005771077)
  ·
    refine ⟨5332404500276062688582077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28439490668139001005771077 5332404500276062688582077)
    ·
      refine ⟨1999651687603523508218279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5332404500276062688582077 1999651687603523508218279)
      ·
        refine ⟨2999477531405285262327419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1999651687603523508218279 2999477531405285262327419)
        ·
          refine ⟨4499216297107927893491129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2999477531405285262327419 4499216297107927893491129)
          ·
            refine ⟨3374412222830945920118347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4499216297107927893491129 3374412222830945920118347)
            ·
              refine ⟨5061618334246418880177521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3374412222830945920118347 5061618334246418880177521)
              ·
                refine ⟨3796213750684814160133141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5061618334246418880177521 3796213750684814160133141)
                ·
                  refine ⟨177947519563350663756241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3796213750684814160133141 177947519563350663756241)
                  ·
                    rfl

theorem cell21_779741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_779741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_779741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_779741 prefixEnd_779741 := by exact prefixLift 779741
  have htrace : WordTrace (prefixWord ++ tailWord_779741) baseStart_779741 baseEnd_779741 := by
    simpa [prefixWord, tailWord_779741, baseEnd_779741] using wordTrace_append hprefix tailTrace_779741
  have hstable : (prefixWord ++ tailWord_779741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779741).length < 2 ^ (prefixWord ++ tailWord_779741).sum := by decide
  have hdescent : baseEnd_779741 < baseStart_779741 := by decide
  rcases family_descends (prefixWord ++ tailWord_779741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779806 : List Nat := [4, 3, 3, 1, 1, 9]
def baseStart_779806 : Nat := 118140960795 + 779806 * 2 ^ 59
def prefixEnd_779806 : Nat := 4983230072969 + 3 ^ 40 * 779806 * 2
def baseEnd_779806 : Nat := 6591198275886110932325

theorem tailTrace_779806 : CollatzResearch.WordTrace tailWord_779806 prefixEnd_779806 6591198275886110932325 := by
  unfold tailWord_779806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3555232676612939638360909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18961240941935678071258181 3555232676612939638360909)
  ·
    refine ⟨1333212253729852364385341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3555232676612939638360909 1333212253729852364385341)
    ·
      refine ⟨499954595148694636644503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1333212253729852364385341 499954595148694636644503)
      ·
        refine ⟨749931892723041954966755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499954595148694636644503 749931892723041954966755)
        ·
          refine ⟨1124897839084562932450133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 749931892723041954966755 1124897839084562932450133)
          ·
            refine ⟨6591198275886110932325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1124897839084562932450133 6591198275886110932325)
            ·
              rfl

theorem cell21_779806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 9].length) (baseStart_779806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_779806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_779806 prefixEnd_779806 := by exact prefixLift 779806
  have htrace : WordTrace (prefixWord ++ tailWord_779806) baseStart_779806 baseEnd_779806 := by
    simpa [prefixWord, tailWord_779806, baseEnd_779806] using wordTrace_append hprefix tailTrace_779806
  have hstable : (prefixWord ++ tailWord_779806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779806).length < 2 ^ (prefixWord ++ tailWord_779806).sum := by decide
  have hdescent : baseEnd_779806 < baseStart_779806 := by decide
  rcases family_descends (prefixWord ++ tailWord_779806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779831 : List Nat := [1, 1, 3, 1, 2, 4, 3, 6]
def baseStart_779831 : Nat := 118140960795 + 779831 * 2 ^ 59
def prefixEnd_779831 : Nat := 4983230072969 + 3 ^ 40 * 779831 * 2
def baseEnd_779831 : Nat := 59322686263176835752019

theorem tailTrace_779831 : CollatzResearch.WordTrace tailWord_779831 prefixEnd_779831 59322686263176835752019 := by
  unfold tailWord_779831
  simp only [CollatzResearch.WordTrace]
  refine ⟨28442773237812946376547347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18961848825208630917698231 28442773237812946376547347)
  ·
    refine ⟨42664159856719419564821021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28442773237812946376547347 42664159856719419564821021)
    ·
      refine ⟨15999059946269782336807883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42664159856719419564821021 15999059946269782336807883)
      ·
        refine ⟨23998589919404673505211825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15999059946269782336807883 23998589919404673505211825)
        ·
          refine ⟨17998942439553505128908869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23998589919404673505211825 17998942439553505128908869)
          ·
            refine ⟨3374801707416282211670413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17998942439553505128908869 3374801707416282211670413)
            ·
              refine ⟨1265550640281105829376405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3374801707416282211670413 1265550640281105829376405)
              ·
                refine ⟨59322686263176835752019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1265550640281105829376405 59322686263176835752019)
                ·
                  rfl

theorem cell21_779831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 6].length) (baseStart_779831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_779831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_779831 prefixEnd_779831 := by exact prefixLift 779831
  have htrace : WordTrace (prefixWord ++ tailWord_779831) baseStart_779831 baseEnd_779831 := by
    simpa [prefixWord, tailWord_779831, baseEnd_779831] using wordTrace_append hprefix tailTrace_779831
  have hstable : (prefixWord ++ tailWord_779831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779831).length < 2 ^ (prefixWord ++ tailWord_779831).sum := by decide
  have hdescent : baseEnd_779831 < baseStart_779831 := by decide
  rcases family_descends (prefixWord ++ tailWord_779831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779879 : List Nat := [1, 1, 5, 1, 1, 1, 4, 4, 3]
def baseStart_779879 : Nat := 118140960795 + 779879 * 2 ^ 59
def prefixEnd_779879 : Nat := 4983230072969 + 3 ^ 40 * 779879 * 2
def baseEnd_779879 : Nat := 177979013043493090455959

theorem tailTrace_779879 : CollatzResearch.WordTrace tailWord_779879 prefixEnd_779879 177979013043493090455959 := by
  unfold tailWord_779879
  simp only [CollatzResearch.WordTrace]
  refine ⟨28444523941639050574294691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18963015961092700382863127 28444523941639050574294691)
  ·
    refine ⟨42666785912458575861442037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28444523941639050574294691 42666785912458575861442037)
    ·
      refine ⟨4000011179292991487010191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42666785912458575861442037 4000011179292991487010191)
      ·
        refine ⟨6000016768939487230515287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4000011179292991487010191 6000016768939487230515287)
        ·
          refine ⟨9000025153409230845772931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6000016768939487230515287 9000025153409230845772931)
          ·
            refine ⟨13500037730113846268659397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9000025153409230845772931 13500037730113846268659397)
            ·
              refine ⟨2531257074396346175373637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13500037730113846268659397 2531257074396346175373637)
              ·
                refine ⟨474610701449314907882557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2531257074396346175373637 474610701449314907882557)
                ·
                  refine ⟨177979013043493090455959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 474610701449314907882557 177979013043493090455959)
                  ·
                    rfl

theorem cell21_779879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 4, 3].length) (baseStart_779879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_779879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_779879 prefixEnd_779879 := by exact prefixLift 779879
  have htrace : WordTrace (prefixWord ++ tailWord_779879) baseStart_779879 baseEnd_779879 := by
    simpa [prefixWord, tailWord_779879, baseEnd_779879] using wordTrace_append hprefix tailTrace_779879
  have hstable : (prefixWord ++ tailWord_779879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779879).length < 2 ^ (prefixWord ++ tailWord_779879).sum := by decide
  have hdescent : baseEnd_779879 < baseStart_779879 := by decide
  rcases family_descends (prefixWord ++ tailWord_779879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779944 : List Nat := [2, 1, 7, 1, 1, 1, 1, 3, 4]
def baseStart_779944 : Nat := 118140960795 + 779944 * 2 ^ 59
def prefixEnd_779944 : Nat := 4983230072969 + 3 ^ 40 * 779944 * 2
def baseEnd_779944 : Nat := 177993846929067421872493

theorem tailTrace_779944 : CollatzResearch.WordTrace tailWord_779944 prefixEnd_779944 177993846929067421872493 := by
  unfold tailWord_779944
  simp only [CollatzResearch.WordTrace]
  refine ⟨14223447343201783337705443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18964596457602377783607257 14223447343201783337705443)
  ·
    refine ⟨21335171014802675006558165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14223447343201783337705443 21335171014802675006558165)
    ·
      refine ⟨500043070659437695466207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 21335171014802675006558165 500043070659437695466207)
      ·
        refine ⟨750064605989156543199311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500043070659437695466207 750064605989156543199311)
        ·
          refine ⟨1125096908983734814798967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 750064605989156543199311 1125096908983734814798967)
          ·
            refine ⟨1687645363475602222198451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1125096908983734814798967 1687645363475602222198451)
            ·
              refine ⟨2531468045213403333297677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1687645363475602222198451 2531468045213403333297677)
              ·
                refine ⟨949300516955026249986629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2531468045213403333297677 949300516955026249986629)
                ·
                  refine ⟨177993846929067421872493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 949300516955026249986629 177993846929067421872493)
                  ·
                    rfl

theorem cell21_779944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 4].length) (baseStart_779944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_779944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_779944 prefixEnd_779944 := by exact prefixLift 779944
  have htrace : WordTrace (prefixWord ++ tailWord_779944) baseStart_779944 baseEnd_779944 := by
    simpa [prefixWord, tailWord_779944, baseEnd_779944] using wordTrace_append hprefix tailTrace_779944
  have hstable : (prefixWord ++ tailWord_779944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779944).length < 2 ^ (prefixWord ++ tailWord_779944).sum := by decide
  have hdescent : baseEnd_779944 < baseStart_779944 := by decide
  rcases family_descends (prefixWord ++ tailWord_779944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779986 : List Nat := [3, 2, 2, 2, 2, 2, 2, 2, 4]
def baseStart_779986 : Nat := 118140960795 + 779986 * 2 ^ 59
def prefixEnd_779986 : Nat := 4983230072969 + 3 ^ 40 * 779986 * 2
def baseEnd_779986 : Nat := 178003431901284682172407

theorem tailTrace_779986 : CollatzResearch.WordTrace tailWord_779986 prefixEnd_779986 178003431901284682172407 := by
  unfold tailWord_779986
  simp only [CollatzResearch.WordTrace]
  refine ⟨7112106638062851962109953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18965617701500938565626541 7112106638062851962109953)
  ·
    refine ⟨5334079978547138971582465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7112106638062851962109953 5334079978547138971582465)
    ·
      refine ⟨4000559983910354228686849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5334079978547138971582465 4000559983910354228686849)
      ·
        refine ⟨3000419987932765671515137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4000559983910354228686849 3000419987932765671515137)
        ·
          refine ⟨2250314990949574253636353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3000419987932765671515137 2250314990949574253636353)
          ·
            refine ⟨1687736243212180690227265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2250314990949574253636353 1687736243212180690227265)
            ·
              refine ⟨1265802182409135517670449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1687736243212180690227265 1265802182409135517670449)
              ·
                refine ⟨949351636806851638252837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1265802182409135517670449 949351636806851638252837)
                ·
                  refine ⟨178003431901284682172407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 949351636806851638252837 178003431901284682172407)
                  ·
                    rfl

theorem cell21_779986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_779986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_779986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_779986 prefixEnd_779986 := by exact prefixLift 779986
  have htrace : WordTrace (prefixWord ++ tailWord_779986) baseStart_779986 baseEnd_779986 := by
    simpa [prefixWord, tailWord_779986, baseEnd_779986] using wordTrace_append hprefix tailTrace_779986
  have hstable : (prefixWord ++ tailWord_779986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779986).length < 2 ^ (prefixWord ++ tailWord_779986).sum := by decide
  have hdescent : baseEnd_779986 < baseStart_779986 := by decide
  rcases family_descends (prefixWord ++ tailWord_779986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780014 : List Nat := [4, 1, 2, 1, 1, 2, 3, 2, 5]
def baseStart_780014 : Nat := 118140960795 + 780014 * 2 ^ 59
def prefixEnd_780014 : Nat := 4983230072969 + 3 ^ 40 * 780014 * 2
def baseEnd_780014 : Nat := 178009821882762855705683

theorem tailTrace_780014 : CollatzResearch.WordTrace tailWord_780014 prefixEnd_780014 178009821882762855705683 := by
  unfold tailWord_780014
  simp only [CollatzResearch.WordTrace]
  refine ⟨3556180974518746078807387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18966298530766645753639397 3556180974518746078807387)
  ·
    refine ⟨5334271461778119118211081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3556180974518746078807387 5334271461778119118211081)
    ·
      refine ⟨4000703596333589338658311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5334271461778119118211081 4000703596333589338658311)
      ·
        refine ⟨6001055394500384007987467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4000703596333589338658311 6001055394500384007987467)
        ·
          refine ⟨9001583091750576011981201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6001055394500384007987467 9001583091750576011981201)
          ·
            refine ⟨6751187318812932008985901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9001583091750576011981201 6751187318812932008985901)
            ·
              refine ⟨2531695244554849503369713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6751187318812932008985901 2531695244554849503369713)
              ·
                refine ⟨1898771433416137127527285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2531695244554849503369713 1898771433416137127527285)
                ·
                  refine ⟨178009821882762855705683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1898771433416137127527285 178009821882762855705683)
                  ·
                    rfl

theorem cell21_780014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_780014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_780014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_780014 prefixEnd_780014 := by exact prefixLift 780014
  have htrace : WordTrace (prefixWord ++ tailWord_780014) baseStart_780014 baseEnd_780014 := by
    simpa [prefixWord, tailWord_780014, baseEnd_780014] using wordTrace_append hprefix tailTrace_780014
  have hstable : (prefixWord ++ tailWord_780014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780014).length < 2 ^ (prefixWord ++ tailWord_780014).sum := by decide
  have hdescent : baseEnd_780014 < baseStart_780014 := by decide
  rcases family_descends (prefixWord ++ tailWord_780014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780028 : List Nat := [2, 2, 2, 1, 3, 1, 2, 2, 6]
def baseStart_780028 : Nat := 118140960795 + 780028 * 2 ^ 59
def prefixEnd_780028 : Nat := 4983230072969 + 3 ^ 40 * 780028 * 2
def baseEnd_780028 : Nat := 178013016873501942472321

theorem tailTrace_780028 : CollatzResearch.WordTrace tailWord_780028 prefixEnd_780028 178013016873501942472321 := by
  unfold tailWord_780028
  simp only [CollatzResearch.WordTrace]
  refine ⟨14224979209049624510734369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18966638945399499347645825 14224979209049624510734369)
  ·
    refine ⟨10668734406787218383050777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14224979209049624510734369 10668734406787218383050777)
    ·
      refine ⟨8001550805090413787288083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10668734406787218383050777 8001550805090413787288083)
      ·
        refine ⟨12002326207635620680932125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8001550805090413787288083 12002326207635620680932125)
        ·
          refine ⟨4500872327863357755349547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12002326207635620680932125 4500872327863357755349547)
          ·
            refine ⟨6751308491795036633024321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4500872327863357755349547 6751308491795036633024321)
            ·
              refine ⟨5063481368846277474768241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6751308491795036633024321 5063481368846277474768241)
              ·
                refine ⟨3797611026634708106076181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5063481368846277474768241 3797611026634708106076181)
                ·
                  refine ⟨178013016873501942472321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3797611026634708106076181 178013016873501942472321)
                  ·
                    rfl

theorem cell21_780028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_780028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_780028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_780028 prefixEnd_780028 := by exact prefixLift 780028
  have htrace : WordTrace (prefixWord ++ tailWord_780028) baseStart_780028 baseEnd_780028 := by
    simpa [prefixWord, tailWord_780028, baseEnd_780028] using wordTrace_append hprefix tailTrace_780028
  have hstable : (prefixWord ++ tailWord_780028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780028).length < 2 ^ (prefixWord ++ tailWord_780028).sum := by decide
  have hdescent : baseEnd_780028 < baseStart_780028 := by decide
  rcases family_descends (prefixWord ++ tailWord_780028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780076 : List Nat := [2, 2, 1, 1, 1, 7, 2, 5]
def baseStart_780076 : Nat := 118140960795 + 780076 * 2 ^ 59
def prefixEnd_780076 : Nat := 4983230072969 + 3 ^ 40 * 780076 * 2
def baseEnd_780076 : Nat := 59341323709154841890741

theorem tailTrace_780076 : CollatzResearch.WordTrace tailWord_780076 prefixEnd_780076 59341323709154841890741 := by
  unfold tailWord_780076
  simp only [CollatzResearch.WordTrace]
  refine ⟨14225854560962676609608041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18967806081283568812810721 14225854560962676609608041)
  ·
    refine ⟨10669390920722007457206031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14225854560962676609608041 10669390920722007457206031)
    ·
      refine ⟨16004086381083011185809047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10669390920722007457206031 16004086381083011185809047)
      ·
        refine ⟨24006129571624516778713571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16004086381083011185809047 24006129571624516778713571)
        ·
          refine ⟨36009194357436775168070357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24006129571624516778713571 36009194357436775168070357)
          ·
            refine ⟨843965492752424418001649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 36009194357436775168070357 843965492752424418001649)
            ·
              refine ⟨632974119564318313501237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 843965492752424418001649 632974119564318313501237)
              ·
                refine ⟨59341323709154841890741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 632974119564318313501237 59341323709154841890741)
                ·
                  rfl

theorem cell21_780076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 5].length) (baseStart_780076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_780076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_780076 prefixEnd_780076 := by exact prefixLift 780076
  have htrace : WordTrace (prefixWord ++ tailWord_780076) baseStart_780076 baseEnd_780076 := by
    simpa [prefixWord, tailWord_780076, baseEnd_780076] using wordTrace_append hprefix tailTrace_780076
  have hstable : (prefixWord ++ tailWord_780076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780076).length < 2 ^ (prefixWord ++ tailWord_780076).sum := by decide
  have hdescent : baseEnd_780076 < baseStart_780076 := by decide
  rcases family_descends (prefixWord ++ tailWord_780076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780104 : List Nat := [2, 1, 3, 1, 1, 4, 2, 1, 6]
def baseStart_780104 : Nat := 118140960795 + 780104 * 2 ^ 59
def prefixEnd_780104 : Nat := 4983230072969 + 3 ^ 40 * 780104 * 2
def baseEnd_780104 : Nat := 178030361108942699205499

theorem tailTrace_780104 : CollatzResearch.WordTrace tailWord_780104 prefixEnd_780104 178030361108942699205499 := by
  unfold tailWord_780104
  simp only [CollatzResearch.WordTrace]
  refine ⟨14226365182911957000617683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18968486910549276000823577 14226365182911957000617683)
  ·
    refine ⟨21339547774367935500926525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14226365182911957000617683 21339547774367935500926525)
    ·
      refine ⟨8002330415387975812847447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21339547774367935500926525 8002330415387975812847447)
      ·
        refine ⟨12003495623081963719271171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8002330415387975812847447 12003495623081963719271171)
        ·
          refine ⟨18005243434622945578906757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12003495623081963719271171 18005243434622945578906757)
          ·
            refine ⟨3375983143991802296045017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18005243434622945578906757 3375983143991802296045017)
            ·
              refine ⟨2531987357993851722033763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3375983143991802296045017 2531987357993851722033763)
              ·
                refine ⟨3797981036990777583050645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2531987357993851722033763 3797981036990777583050645)
                ·
                  refine ⟨178030361108942699205499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3797981036990777583050645 178030361108942699205499)
                  ·
                    rfl

theorem cell21_780104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 6].length) (baseStart_780104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_780104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_780104 prefixEnd_780104 := by exact prefixLift 780104
  have htrace : WordTrace (prefixWord ++ tailWord_780104) baseStart_780104 baseEnd_780104 := by
    simpa [prefixWord, tailWord_780104, baseEnd_780104] using wordTrace_append hprefix tailTrace_780104
  have hstable : (prefixWord ++ tailWord_780104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780104).length < 2 ^ (prefixWord ++ tailWord_780104).sum := by decide
  have hdescent : baseEnd_780104 < baseStart_780104 := by decide
  rcases family_descends (prefixWord ++ tailWord_780104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780158 : List Nat := [4, 2, 3, 1, 1, 3, 2, 2, 3]
def baseStart_780158 : Nat := 118140960795 + 780158 * 2 ^ 59
def prefixEnd_780158 : Nat := 4983230072969 + 3 ^ 40 * 780158 * 2
def baseEnd_780158 : Nat := 178042684644650605305389

theorem tailTrace_780158 : CollatzResearch.WordTrace tailWord_780158 prefixEnd_780158 178042684644650605305389 := by
  unfold tailWord_780158
  simp only [CollatzResearch.WordTrace]
  refine ⟨3556837488453535152962641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18969799938418854149134085 3556837488453535152962641)
  ·
    refine ⟨2667628116340151364721981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3556837488453535152962641 2667628116340151364721981)
    ·
      refine ⟨1000360543627556761770743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2667628116340151364721981 1000360543627556761770743)
      ·
        refine ⟨1500540815441335142656115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1000360543627556761770743 1500540815441335142656115)
        ·
          refine ⟨2250811223162002713984173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1500540815441335142656115 2250811223162002713984173)
          ·
            refine ⟨844054208685751017744065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2250811223162002713984173 844054208685751017744065)
            ·
              refine ⟨633040656514313263308049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 844054208685751017744065 633040656514313263308049)
              ·
                refine ⟨474780492385734947481037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 633040656514313263308049 474780492385734947481037)
                ·
                  refine ⟨178042684644650605305389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 474780492385734947481037 178042684644650605305389)
                  ·
                    rfl

theorem cell21_780158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_780158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_780158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_780158 prefixEnd_780158 := by exact prefixLift 780158
  have htrace : WordTrace (prefixWord ++ tailWord_780158) baseStart_780158 baseEnd_780158 := by
    simpa [prefixWord, tailWord_780158, baseEnd_780158] using wordTrace_append hprefix tailTrace_780158
  have hstable : (prefixWord ++ tailWord_780158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780158).length < 2 ^ (prefixWord ++ tailWord_780158).sum := by decide
  have hdescent : baseEnd_780158 < baseStart_780158 := by decide
  rcases family_descends (prefixWord ++ tailWord_780158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780259 : List Nat := [1, 1, 1, 6, 1, 2, 3, 3, 3]
def baseStart_780259 : Nat := 118140960795 + 780259 * 2 ^ 59
def prefixEnd_780259 : Nat := 4983230072969 + 3 ^ 40 * 780259 * 2
def baseEnd_780259 : Nat := 178065734220696874121849

theorem tailTrace_780259 : CollatzResearch.WordTrace tailWord_780259 prefixEnd_780259 178065734220696874121849 := by
  unfold tailWord_780259
  simp only [CollatzResearch.WordTrace]
  refine ⟨28458383680262375473127831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18972255786841583648751887 28458383680262375473127831)
  ·
    refine ⟨42687575520393563209691747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28458383680262375473127831 42687575520393563209691747)
    ·
      refine ⟨64031363280590344814537621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42687575520393563209691747 64031363280590344814537621)
      ·
        refine ⟨3001470153777672413181451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 64031363280590344814537621 3001470153777672413181451)
        ·
          refine ⟨4502205230666508619772177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3001470153777672413181451 4502205230666508619772177)
          ·
            refine ⟨3376653922999881464829133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4502205230666508619772177 3376653922999881464829133)
            ·
              refine ⟨1266245221124955549310925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3376653922999881464829133 1266245221124955549310925)
              ·
                refine ⟨474841957921858330991597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1266245221124955549310925 474841957921858330991597)
                ·
                  refine ⟨178065734220696874121849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 474841957921858330991597 178065734220696874121849)
                  ·
                    rfl

theorem cell21_780259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 3, 3].length) (baseStart_780259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_780259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_780259 prefixEnd_780259 := by exact prefixLift 780259
  have htrace : WordTrace (prefixWord ++ tailWord_780259) baseStart_780259 baseEnd_780259 := by
    simpa [prefixWord, tailWord_780259, baseEnd_780259] using wordTrace_append hprefix tailTrace_780259
  have hstable : (prefixWord ++ tailWord_780259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780259).length < 2 ^ (prefixWord ++ tailWord_780259).sum := by decide
  have hdescent : baseEnd_780259 < baseStart_780259 := by decide
  rcases family_descends (prefixWord ++ tailWord_780259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780315 : List Nat := [1, 1, 1, 1, 1, 1, 3, 6, 6]
def baseStart_780315 : Nat := 118140960795 + 780315 * 2 ^ 59
def prefixEnd_780315 : Nat := 4983230072969 + 3 ^ 40 * 780315 * 2
def baseEnd_780315 : Nat := 178078514183653221188401

theorem tailTrace_780315 : CollatzResearch.WordTrace tailWord_780315 prefixEnd_780315 178078514183653221188401 := by
  unfold tailWord_780315
  simp only [CollatzResearch.WordTrace]
  refine ⟨28460426168059497037166399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18973617445372998024777599 28460426168059497037166399)
  ·
    refine ⟨42690639252089245555749599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28460426168059497037166399 42690639252089245555749599)
    ·
      refine ⟨64035958878133868333624399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42690639252089245555749599 64035958878133868333624399)
      ·
        refine ⟨96053938317200802500436599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64035958878133868333624399 96053938317200802500436599)
        ·
          refine ⟨144080907475801203750654899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96053938317200802500436599 144080907475801203750654899)
          ·
            refine ⟨216121361213701805625982349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144080907475801203750654899 216121361213701805625982349)
            ·
              refine ⟨81045510455138177109743381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216121361213701805625982349 81045510455138177109743381)
              ·
                refine ⟨3799008302584602052019221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81045510455138177109743381 3799008302584602052019221)
                ·
                  refine ⟨178078514183653221188401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3799008302584602052019221 178078514183653221188401)
                  ·
                    rfl

theorem cell21_780315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 6].length) (baseStart_780315 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_780315 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_780315 prefixEnd_780315 := by exact prefixLift 780315
  have htrace : WordTrace (prefixWord ++ tailWord_780315) baseStart_780315 baseEnd_780315 := by
    simpa [prefixWord, tailWord_780315, baseEnd_780315] using wordTrace_append hprefix tailTrace_780315
  have hstable : (prefixWord ++ tailWord_780315).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780315).length < 2 ^ (prefixWord ++ tailWord_780315).sum := by decide
  have hdescent : baseEnd_780315 < baseStart_780315 := by decide
  rcases family_descends (prefixWord ++ tailWord_780315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780439 : List Nat := [1, 1, 3, 3, 4, 2, 7]
def baseStart_780439 : Nat := 118140960795 + 780439 * 2 ^ 59
def prefixEnd_780439 : Nat := 4983230072969 + 3 ^ 40 * 780439 * 2
def baseEnd_780439 : Nat := 19789645852561840124609

theorem tailTrace_780439 : CollatzResearch.WordTrace tailWord_780439 prefixEnd_780439 19789645852561840124609 := by
  unfold tailWord_780439
  simp only [CollatzResearch.WordTrace]
  refine ⟨28464948819610266214680371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18976632546406844143120247 28464948819610266214680371)
  ·
    refine ⟨42697423229415399322020557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28464948819610266214680371 42697423229415399322020557)
    ·
      refine ⟨16011533711030774745757709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42697423229415399322020557 16011533711030774745757709)
      ·
        refine ⟨6004325141636540529659141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16011533711030774745757709 6004325141636540529659141)
        ·
          refine ⟨1125810964056851349311089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6004325141636540529659141 1125810964056851349311089)
          ·
            refine ⟨844358223042638511983317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1125810964056851349311089 844358223042638511983317)
            ·
              refine ⟨19789645852561840124609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 844358223042638511983317 19789645852561840124609)
              ·
                rfl

theorem cell21_780439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 7].length) (baseStart_780439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_780439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_780439 prefixEnd_780439 := by exact prefixLift 780439
  have htrace : WordTrace (prefixWord ++ tailWord_780439) baseStart_780439 baseEnd_780439 := by
    simpa [prefixWord, tailWord_780439, baseEnd_780439] using wordTrace_append hprefix tailTrace_780439
  have hstable : (prefixWord ++ tailWord_780439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780439).length < 2 ^ (prefixWord ++ tailWord_780439).sum := by decide
  have hdescent : baseEnd_780439 < baseStart_780439 := by decide
  rcases family_descends (prefixWord ++ tailWord_780439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780498 : List Nat := [3, 2, 2, 2, 1, 11]
def baseStart_780498 : Nat := 118140960795 + 780498 * 2 ^ 59
def prefixEnd_780498 : Nat := 4983230072969 + 3 ^ 40 * 780498 * 2
def baseEnd_780498 : Nat := 6597047306551317394001

theorem tailTrace_780498 : CollatzResearch.WordTrace tailWord_780498 prefixEnd_780498 6597047306551317394001 := by
  unfold tailWord_780498
  simp only [CollatzResearch.WordTrace]
  refine ⟨7116775181599129822769537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18978067150931012860718765 7116775181599129822769537)
  ·
    refine ⟨5337581386199347367077153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7116775181599129822769537 5337581386199347367077153)
    ·
      refine ⟨4003186039649510525307865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5337581386199347367077153 4003186039649510525307865)
      ·
        refine ⟨3002389529737132893980899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4003186039649510525307865 3002389529737132893980899)
        ·
          refine ⟨4503584294605699340971349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3002389529737132893980899 4503584294605699340971349)
          ·
            refine ⟨6597047306551317394001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4503584294605699340971349 6597047306551317394001)
            ·
              rfl

theorem cell21_780498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 11].length) (baseStart_780498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_780498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_780498 prefixEnd_780498 := by exact prefixLift 780498
  have htrace : WordTrace (prefixWord ++ tailWord_780498) baseStart_780498 baseEnd_780498 := by
    simpa [prefixWord, tailWord_780498, baseEnd_780498] using wordTrace_append hprefix tailTrace_780498
  have hstable : (prefixWord ++ tailWord_780498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780498).length < 2 ^ (prefixWord ++ tailWord_780498).sum := by decide
  have hdescent : baseEnd_780498 < baseStart_780498 := by decide
  rcases family_descends (prefixWord ++ tailWord_780498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780504 : List Nat := [2, 1, 2, 2, 4, 3, 2, 2, 3]
def baseStart_780504 : Nat := 118140960795 + 780504 * 2 ^ 59
def prefixEnd_780504 : Nat := 4983230072969 + 3 ^ 40 * 780504 * 2
def baseEnd_780504 : Nat := 178121646558630892538015

theorem tailTrace_780504 : CollatzResearch.WordTrace tailWord_780504 prefixEnd_780504 178121646558630892538015 := by
  unfold tailWord_780504
  simp only [CollatzResearch.WordTrace]
  refine ⟨14233659782187391157898283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18978213042916521543864377 14233659782187391157898283)
  ·
    refine ⟨21350489673281086736847425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14233659782187391157898283 21350489673281086736847425)
    ·
      refine ⟨16012867254960815052635569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21350489673281086736847425 16012867254960815052635569)
      ·
        refine ⟨12009650441220611289476677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16012867254960815052635569 12009650441220611289476677)
        ·
          refine ⟨2251809457728864616776877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12009650441220611289476677 2251809457728864616776877)
          ·
            refine ⟨844428546648324231291329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2251809457728864616776877 844428546648324231291329)
            ·
              refine ⟨633321409986243173468497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 844428546648324231291329 633321409986243173468497)
              ·
                refine ⟨474991057489682380101373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 633321409986243173468497 474991057489682380101373)
                ·
                  refine ⟨178121646558630892538015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 474991057489682380101373 178121646558630892538015)
                  ·
                    rfl

theorem cell21_780504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 2, 3].length) (baseStart_780504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_780504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_780504 prefixEnd_780504 := by exact prefixLift 780504
  have htrace : WordTrace (prefixWord ++ tailWord_780504) baseStart_780504 baseEnd_780504 := by
    simpa [prefixWord, tailWord_780504, baseEnd_780504] using wordTrace_append hprefix tailTrace_780504
  have hstable : (prefixWord ++ tailWord_780504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780504).length < 2 ^ (prefixWord ++ tailWord_780504).sum := by decide
  have hdescent : baseEnd_780504 < baseStart_780504 := by decide
  rcases family_descends (prefixWord ++ tailWord_780504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780543 : List Nat := [1, 1, 2, 2, 1, 4, 2, 2, 6]
def baseStart_780543 : Nat := 118140960795 + 780543 * 2 ^ 59
def prefixEnd_780543 : Nat := 4983230072969 + 3 ^ 40 * 780543 * 2
def baseEnd_780543 : Nat := 178130546889975491387935

theorem tailTrace_780543 : CollatzResearch.WordTrace tailWord_780543 prefixEnd_780543 178130546889975491387935 := by
  unfold tailWord_780543
  simp only [CollatzResearch.WordTrace]
  refine ⟨28468742011233491976466283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18979161340822327984310855 28468742011233491976466283)
  ·
    refine ⟨42703113016850237964699425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28468742011233491976466283 42703113016850237964699425)
    ·
      refine ⟨32027334762637678473524569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42703113016850237964699425 32027334762637678473524569)
      ·
        refine ⟨24020501071978258855143427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32027334762637678473524569 24020501071978258855143427)
        ·
          refine ⟨36030751607967388282715141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24020501071978258855143427 36030751607967388282715141)
          ·
            refine ⟨6755765926493885303009089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36030751607967388282715141 6755765926493885303009089)
            ·
              refine ⟨5066824444870413977256817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6755765926493885303009089 5066824444870413977256817)
              ·
                refine ⟨3800118333652810482942613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5066824444870413977256817 3800118333652810482942613)
                ·
                  refine ⟨178130546889975491387935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3800118333652810482942613 178130546889975491387935)
                  ·
                    rfl

theorem cell21_780543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 6].length) (baseStart_780543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_780543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_780543 prefixEnd_780543 := by exact prefixLift 780543
  have htrace : WordTrace (prefixWord ++ tailWord_780543) baseStart_780543 baseEnd_780543 := by
    simpa [prefixWord, tailWord_780543, baseEnd_780543] using wordTrace_append hprefix tailTrace_780543
  have hstable : (prefixWord ++ tailWord_780543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780543).length < 2 ^ (prefixWord ++ tailWord_780543).sum := by decide
  have hdescent : baseEnd_780543 < baseStart_780543 := by decide
  rcases family_descends (prefixWord ++ tailWord_780543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780583 : List Nat := [1, 1, 8, 1, 2, 1, 2, 5]
def baseStart_780583 : Nat := 118140960795 + 780583 * 2 ^ 59
def prefixEnd_780583 : Nat := 4983230072969 + 3 ^ 40 * 780583 * 2
def baseEnd_780583 : Nat := 59379891811648103573729

theorem tailTrace_780583 : CollatzResearch.WordTrace tailWord_780583 prefixEnd_780583 59379891811648103573729 := by
  unfold tailWord_780583
  simp only [CollatzResearch.WordTrace]
  refine ⟨28470200931088578807922403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18980133954059052538614935 28470200931088578807922403)
  ·
    refine ⟨42705301396632868211883605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28470200931088578807922403 42705301396632868211883605)
    ·
      refine ⟨500452750741791424358011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 42705301396632868211883605 500452750741791424358011)
      ·
        refine ⟨750679126112687136537017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500452750741791424358011 750679126112687136537017)
        ·
          refine ⟨563009344584515352402763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 750679126112687136537017 563009344584515352402763)
          ·
            refine ⟨844514016876773028604145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563009344584515352402763 844514016876773028604145)
            ·
              refine ⟨633385512657579771453109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 844514016876773028604145 633385512657579771453109)
              ·
                refine ⟨59379891811648103573729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 633385512657579771453109 59379891811648103573729)
                ·
                  rfl

theorem cell21_780583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 5].length) (baseStart_780583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_780583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_780583 prefixEnd_780583 := by exact prefixLift 780583
  have htrace : WordTrace (prefixWord ++ tailWord_780583) baseStart_780583 baseEnd_780583 := by
    simpa [prefixWord, tailWord_780583, baseEnd_780583] using wordTrace_append hprefix tailTrace_780583
  have hstable : (prefixWord ++ tailWord_780583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780583).length < 2 ^ (prefixWord ++ tailWord_780583).sum := by decide
  have hdescent : baseEnd_780583 < baseStart_780583 := by decide
  rcases family_descends (prefixWord ++ tailWord_780583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780729 : List Nat := [1, 2, 1, 4, 3, 3, 1, 2, 4]
def baseStart_780729 : Nat := 118140960795 + 780729 * 2 ^ 59
def prefixEnd_780729 : Nat := 4983230072969 + 3 ^ 40 * 780729 * 2
def baseEnd_780729 : Nat := 178172994624080501287555

theorem tailTrace_780729 : CollatzResearch.WordTrace tailWord_780729 prefixEnd_780729 178172994624080501287555 := by
  unfold tailWord_780729
  simp only [CollatzResearch.WordTrace]
  refine ⟨28475525988559645742737241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18983683992373097161824827 28475525988559645742737241)
  ·
    refine ⟨21356644491419734307052931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28475525988559645742737241 21356644491419734307052931)
    ·
      refine ⟨32034966737129601460579397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21356644491419734307052931 32034966737129601460579397)
      ·
        refine ⟨6006556263211800273858637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32034966737129601460579397 6006556263211800273858637)
        ·
          refine ⟨2252458598704425102696989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6006556263211800273858637 2252458598704425102696989)
          ·
            refine ⟨844671974514159413511371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2252458598704425102696989 844671974514159413511371)
            ·
              refine ⟨1267007961771239120267057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 844671974514159413511371 1267007961771239120267057)
              ·
                refine ⟨950255971328429340200293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1267007961771239120267057 950255971328429340200293)
                ·
                  refine ⟨178172994624080501287555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 950255971328429340200293 178172994624080501287555)
                  ·
                    rfl

theorem cell21_780729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 4].length) (baseStart_780729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_780729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_780729 prefixEnd_780729 := by exact prefixLift 780729
  have htrace : WordTrace (prefixWord ++ tailWord_780729) baseStart_780729 baseEnd_780729 := by
    simpa [prefixWord, tailWord_780729, baseEnd_780729] using wordTrace_append hprefix tailTrace_780729
  have hstable : (prefixWord ++ tailWord_780729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780729).length < 2 ^ (prefixWord ++ tailWord_780729).sum := by decide
  have hdescent : baseEnd_780729 < baseStart_780729 := by decide
  rcases family_descends (prefixWord ++ tailWord_780729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780757 : List Nat := [1, 3, 2, 3, 1, 2, 2, 2, 5]
def baseStart_780757 : Nat := 118140960795 + 780757 * 2 ^ 59
def prefixEnd_780757 : Nat := 4983230072969 + 3 ^ 40 * 780757 * 2
def baseEnd_780757 : Nat := 178179384605558674820831

theorem tailTrace_780757 : CollatzResearch.WordTrace tailWord_780757 prefixEnd_780757 178179384605558674820831 := by
  unfold tailWord_780757
  simp only [CollatzResearch.WordTrace]
  refine ⟨28476547232458206524756525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18984364821638804349837683 28476547232458206524756525)
  ·
    refine ⟨10678705212171827446783697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28476547232458206524756525 10678705212171827446783697)
    ·
      refine ⟨8009028909128870585087773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10678705212171827446783697 8009028909128870585087773)
      ·
        refine ⟨3003385840923326469407915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8009028909128870585087773 3003385840923326469407915)
        ·
          refine ⟨4505078761384989704111873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3003385840923326469407915 4505078761384989704111873)
          ·
            refine ⟨3378809071038742278083905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4505078761384989704111873 3378809071038742278083905)
            ·
              refine ⟨2534106803279056708562929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3378809071038742278083905 2534106803279056708562929)
              ·
                refine ⟨1900580102459292531422197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2534106803279056708562929 1900580102459292531422197)
                ·
                  refine ⟨178179384605558674820831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1900580102459292531422197 178179384605558674820831)
                  ·
                    rfl

theorem cell21_780757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_780757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_780757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_780757 prefixEnd_780757 := by exact prefixLift 780757
  have htrace : WordTrace (prefixWord ++ tailWord_780757) baseStart_780757 baseEnd_780757 := by
    simpa [prefixWord, tailWord_780757, baseEnd_780757] using wordTrace_append hprefix tailTrace_780757
  have hstable : (prefixWord ++ tailWord_780757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780757).length < 2 ^ (prefixWord ++ tailWord_780757).sum := by decide
  have hdescent : baseEnd_780757 < baseStart_780757 := by decide
  rcases family_descends (prefixWord ++ tailWord_780757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780909 : List Nat := [1, 5, 1, 1, 3, 1, 1, 3, 5]
def baseStart_780909 : Nat := 118140960795 + 780909 * 2 ^ 59
def prefixEnd_780909 : Nat := 4983230072969 + 3 ^ 40 * 780909 * 2
def baseEnd_780909 : Nat := 178214073076440188287187

theorem tailTrace_780909 : CollatzResearch.WordTrace tailWord_780909 prefixEnd_780909 178214073076440188287187 := by
  unfold tailWord_780909
  simp only [CollatzResearch.WordTrace]
  refine ⟨28482091127907536484289781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18988060751938357656193187 28482091127907536484289781)
  ·
    refine ⟨2670196043241331545402167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28482091127907536484289781 2670196043241331545402167)
    ·
      refine ⟨4005294064861997318103251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2670196043241331545402167 4005294064861997318103251)
      ·
        refine ⟨6007941097292995977154877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4005294064861997318103251 6007941097292995977154877)
        ·
          refine ⟨2252977911484873491433079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6007941097292995977154877 2252977911484873491433079)
          ·
            refine ⟨3379466867227310237149619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2252977911484873491433079 3379466867227310237149619)
            ·
              refine ⟨5069200300840965355724429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3379466867227310237149619 5069200300840965355724429)
              ·
                refine ⟨1900950112815362008396661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5069200300840965355724429 1900950112815362008396661)
                ·
                  refine ⟨178214073076440188287187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1900950112815362008396661 178214073076440188287187)
                  ·
                    rfl

theorem cell21_780909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_780909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_780909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_780909 prefixEnd_780909 := by exact prefixLift 780909
  have htrace : WordTrace (prefixWord ++ tailWord_780909) baseStart_780909 baseEnd_780909 := by
    simpa [prefixWord, tailWord_780909, baseEnd_780909] using wordTrace_append hprefix tailTrace_780909
  have hstable : (prefixWord ++ tailWord_780909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780909).length < 2 ^ (prefixWord ++ tailWord_780909).sum := by decide
  have hdescent : baseEnd_780909 < baseStart_780909 := by decide
  rcases family_descends (prefixWord ++ tailWord_780909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780974 : List Nat := [4, 1, 4, 1, 1, 1, 4, 1, 4]
def baseStart_780974 : Nat := 118140960795 + 780974 * 2 ^ 59
def prefixEnd_780974 : Nat := 4983230072969 + 3 ^ 40 * 780974 * 2
def baseEnd_780974 : Nat := 178228906962014519703721

theorem tailTrace_780974 : CollatzResearch.WordTrace tailWord_780974 prefixEnd_780974 178228906962014519703721 := by
  unfold tailWord_780974
  simp only [CollatzResearch.WordTrace]
  refine ⟨3560557734084006573175747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18989641248448035056937317 3560557734084006573175747)
  ·
    refine ⟨5340836601126009859763621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3560557734084006573175747 5340836601126009859763621)
    ·
      refine ⟨1001406862711126848705679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5340836601126009859763621 1001406862711126848705679)
      ·
        refine ⟨1502110294066690273058519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1001406862711126848705679 1502110294066690273058519)
        ·
          refine ⟨2253165441100035409587779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1502110294066690273058519 2253165441100035409587779)
          ·
            refine ⟨3379748161650053114381669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2253165441100035409587779 3379748161650053114381669)
            ·
              refine ⟨633702780309384958946563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3379748161650053114381669 633702780309384958946563)
              ·
                refine ⟨950554170464077438419845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 633702780309384958946563 950554170464077438419845)
                ·
                  refine ⟨178228906962014519703721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 950554170464077438419845 178228906962014519703721)
                  ·
                    rfl

theorem cell21_780974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_780974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_780974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_780974 prefixEnd_780974 := by exact prefixLift 780974
  have htrace : WordTrace (prefixWord ++ tailWord_780974) baseStart_780974 baseEnd_780974 := by
    simpa [prefixWord, tailWord_780974, baseEnd_780974] using wordTrace_append hprefix tailTrace_780974
  have hstable : (prefixWord ++ tailWord_780974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780974).length < 2 ^ (prefixWord ++ tailWord_780974).sum := by decide
  have hdescent : baseEnd_780974 < baseStart_780974 := by decide
  rcases family_descends (prefixWord ++ tailWord_780974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781016 : List Nat := [2, 1, 2, 2, 3, 3, 2, 2, 4]
def baseStart_781016 : Nat := 118140960795 + 781016 * 2 ^ 59
def prefixEnd_781016 : Nat := 4983230072969 + 3 ^ 40 * 781016 * 2
def baseEnd_781016 : Nat := 178238491934231780003635

theorem tailTrace_781016 : CollatzResearch.WordTrace tailWord_781016 prefixEnd_781016 178238491934231780003635 := by
  unfold tailWord_781016
  simp only [CollatzResearch.WordTrace]
  refine ⟨14242996869259946879217451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18990662492346595838956601 14242996869259946879217451)
  ·
    refine ⟨21364495303889920318826177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14242996869259946879217451 21364495303889920318826177)
    ·
      refine ⟨16023371477917440239119633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21364495303889920318826177 16023371477917440239119633)
      ·
        refine ⟨12017528608438080179339725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16023371477917440239119633 12017528608438080179339725)
        ·
          refine ⟨4506573228164280067252397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12017528608438080179339725 4506573228164280067252397)
          ·
            refine ⟨1689964960561605025219649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4506573228164280067252397 1689964960561605025219649)
            ·
              refine ⟨1267473720421203768914737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1689964960561605025219649 1267473720421203768914737)
              ·
                refine ⟨950605290315902826686053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1267473720421203768914737 950605290315902826686053)
                ·
                  refine ⟨178238491934231780003635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 950605290315902826686053 178238491934231780003635)
                  ·
                    rfl

theorem cell21_781016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 4].length) (baseStart_781016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_781016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_781016 prefixEnd_781016 := by exact prefixLift 781016
  have htrace : WordTrace (prefixWord ++ tailWord_781016) baseStart_781016 baseEnd_781016 := by
    simpa [prefixWord, tailWord_781016, baseEnd_781016] using wordTrace_append hprefix tailTrace_781016
  have hstable : (prefixWord ++ tailWord_781016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781016).length < 2 ^ (prefixWord ++ tailWord_781016).sum := by decide
  have hdescent : baseEnd_781016 < baseStart_781016 := by decide
  rcases family_descends (prefixWord ++ tailWord_781016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781089 : List Nat := [1, 2, 3, 2, 1, 2, 2, 8]
def baseStart_781089 : Nat := 118140960795 + 781089 * 2 ^ 59
def prefixEnd_781089 : Nat := 4983230072969 + 3 ^ 40 * 781089 * 2
def baseEnd_781089 : Nat := 59418383842933291762273

theorem tailTrace_781089 : CollatzResearch.WordTrace tailWord_781089 prefixEnd_781089 59418383842933291762273 := by
  unfold tailWord_781089
  simp only [CollatzResearch.WordTrace]
  refine ⟨28488656267255427225842321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18992437511503618150561547 28488656267255427225842321)
  ·
    refine ⟨21366492200441570419381741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28488656267255427225842321 21366492200441570419381741)
    ·
      refine ⟨8012434575165588907268153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21366492200441570419381741 8012434575165588907268153)
      ·
        refine ⟨6009325931374191680451115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8012434575165588907268153 6009325931374191680451115)
        ·
          refine ⟨9013988897061287520676673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6009325931374191680451115 9013988897061287520676673)
          ·
            refine ⟨6760491672795965640507505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9013988897061287520676673 6760491672795965640507505)
            ·
              refine ⟨5070368754596974230380629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6760491672795965640507505 5070368754596974230380629)
              ·
                refine ⟨59418383842933291762273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5070368754596974230380629 59418383842933291762273)
                ·
                  rfl

theorem cell21_781089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 8].length) (baseStart_781089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_781089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_781089 prefixEnd_781089 := by exact prefixLift 781089
  have htrace : WordTrace (prefixWord ++ tailWord_781089) baseStart_781089 baseEnd_781089 := by
    simpa [prefixWord, tailWord_781089, baseEnd_781089] using wordTrace_append hprefix tailTrace_781089
  have hstable : (prefixWord ++ tailWord_781089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781089).length < 2 ^ (prefixWord ++ tailWord_781089).sum := by decide
  have hdescent : baseEnd_781089 < baseStart_781089 := by decide
  rcases family_descends (prefixWord ++ tailWord_781089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781151 : List Nat := [1, 1, 2, 3, 1, 3, 3, 3, 4]
def baseStart_781151 : Nat := 118140960795 + 781151 * 2 ^ 59
def prefixEnd_781151 : Nat := 4983230072969 + 3 ^ 40 * 781151 * 2
def baseEnd_781151 : Nat := 178269300773501545253359

theorem tailTrace_781151 : CollatzResearch.WordTrace tailWord_781151 prefixEnd_781151 178269300773501545253359 := by
  unfold tailWord_781151
  simp only [CollatzResearch.WordTrace]
  refine ⟨28490917593030811814599307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18993945062020541209732871 28490917593030811814599307)
  ·
    refine ⟨42736376389546217721898961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28490917593030811814599307 42736376389546217721898961)
    ·
      refine ⟨32052282292159663291424221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42736376389546217721898961 32052282292159663291424221)
      ·
        refine ⟨12019605859559873734284083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32052282292159663291424221 12019605859559873734284083)
        ·
          refine ⟨18029408789339810601426125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12019605859559873734284083 18029408789339810601426125)
          ·
            refine ⟨6761028296002428975534797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18029408789339810601426125 6761028296002428975534797)
            ·
              refine ⟨2535385611000910865825549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6761028296002428975534797 2535385611000910865825549)
              ·
                refine ⟨950769604125341574684581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2535385611000910865825549 950769604125341574684581)
                ·
                  refine ⟨178269300773501545253359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 950769604125341574684581 178269300773501545253359)
                  ·
                    rfl

theorem cell21_781151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 4].length) (baseStart_781151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_781151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_781151 prefixEnd_781151 := by exact prefixLift 781151
  have htrace : WordTrace (prefixWord ++ tailWord_781151) baseStart_781151 baseEnd_781151 := by
    simpa [prefixWord, tailWord_781151, baseEnd_781151] using wordTrace_append hprefix tailTrace_781151
  have hstable : (prefixWord ++ tailWord_781151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781151).length < 2 ^ (prefixWord ++ tailWord_781151).sum := by decide
  have hdescent : baseEnd_781151 < baseStart_781151 := by decide
  rcases family_descends (prefixWord ++ tailWord_781151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781182 : List Nat := [4, 2, 3, 1, 11]
def baseStart_781182 : Nat := 118140960795 + 781182 * 2 ^ 59
def prefixEnd_781182 : Nat := 4983230072969 + 3 ^ 40 * 781182 * 2
def baseEnd_781182 : Nat := 2200942906121634323909

theorem tailTrace_781182 : CollatzResearch.WordTrace tailWord_781182 prefixEnd_781182 2200942906121634323909 := by
  unfold tailWord_781182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3561506031989813013622225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18994698837279002739318533 3561506031989813013622225)
  ·
    refine ⟨2671129523992359760216669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3561506031989813013622225 2671129523992359760216669)
    ·
      refine ⟨1001673571497134910081251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2671129523992359760216669 1001673571497134910081251)
      ·
        refine ⟨1502510357245702365121877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1001673571497134910081251 1502510357245702365121877)
        ·
          refine ⟨2200942906121634323909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1502510357245702365121877 2200942906121634323909)
          ·
            rfl

theorem cell21_781182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 11].length) (baseStart_781182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_781182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_781182 prefixEnd_781182 := by exact prefixLift 781182
  have htrace : WordTrace (prefixWord ++ tailWord_781182) baseStart_781182 baseEnd_781182 := by
    simpa [prefixWord, tailWord_781182, baseEnd_781182] using wordTrace_append hprefix tailTrace_781182
  have hstable : (prefixWord ++ tailWord_781182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781182).length < 2 ^ (prefixWord ++ tailWord_781182).sum := by decide
  have hdescent : baseEnd_781182 < baseStart_781182 := by decide
  rcases family_descends (prefixWord ++ tailWord_781182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781241 : List Nat := [1, 2, 1, 4, 2, 3, 8]
def baseStart_781241 : Nat := 118140960795 + 781241 * 2 ^ 59
def prefixEnd_781241 : Nat := 4983230072969 + 3 ^ 40 * 781241 * 2
def baseEnd_781241 : Nat := 19809982222186820972575

theorem tailTrace_781241 : CollatzResearch.WordTrace tailWord_781241 prefixEnd_781241 19809982222186820972575 := by
  unfold tailWord_781241
  simp only [CollatzResearch.WordTrace]
  refine ⟨28494200162704757185375577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18996133441803171456917051 28494200162704757185375577)
  ·
    refine ⟨21370650122028567889031683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28494200162704757185375577 21370650122028567889031683)
    ·
      refine ⟨32055975183042851833547525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21370650122028567889031683 32055975183042851833547525)
      ·
        refine ⟨6010495346820534718790161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32055975183042851833547525 6010495346820534718790161)
        ·
          refine ⟨4507871510115401039092621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6010495346820534718790161 4507871510115401039092621)
          ·
            refine ⟨1690451816293275389659733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4507871510115401039092621 1690451816293275389659733)
            ·
              refine ⟨19809982222186820972575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1690451816293275389659733 19809982222186820972575)
              ·
                rfl

theorem cell21_781241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 8].length) (baseStart_781241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_781241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_781241 prefixEnd_781241 := by exact prefixLift 781241
  have htrace : WordTrace (prefixWord ++ tailWord_781241) baseStart_781241 baseEnd_781241 := by
    simpa [prefixWord, tailWord_781241, baseEnd_781241] using wordTrace_append hprefix tailTrace_781241
  have hstable : (prefixWord ++ tailWord_781241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781241).length < 2 ^ (prefixWord ++ tailWord_781241).sum := by decide
  have hdescent : baseEnd_781241 < baseStart_781241 := by decide
  rcases family_descends (prefixWord ++ tailWord_781241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781272 : List Nat := [2, 1, 2, 2, 2, 3, 2, 2, 5]
def baseStart_781272 : Nat := 118140960795 + 781272 * 2 ^ 59
def prefixEnd_781272 : Nat := 4983230072969 + 3 ^ 40 * 781272 * 2
def baseEnd_781272 : Nat := 178296914622032223736445

theorem tailTrace_781272 : CollatzResearch.WordTrace tailWord_781272 prefixEnd_781272 178296914622032223736445 := by
  unfold tailWord_781272
  simp only [CollatzResearch.WordTrace]
  refine ⟨14247665412796224739877035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18996887217061632986502713 14247665412796224739877035)
  ·
    refine ⟨21371498119194337109815553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14247665412796224739877035 21371498119194337109815553)
    ·
      refine ⟨16028623589395752832361665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21371498119194337109815553 16028623589395752832361665)
      ·
        refine ⟨12021467692046814624271249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16028623589395752832361665 12021467692046814624271249)
        ·
          refine ⟨9016100769035110968203437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12021467692046814624271249 9016100769035110968203437)
          ·
            refine ⟨3381037788388166613076289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9016100769035110968203437 3381037788388166613076289)
            ·
              refine ⟨2535778341291124959807217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3381037788388166613076289 2535778341291124959807217)
              ·
                refine ⟨1901833755968343719855413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2535778341291124959807217 1901833755968343719855413)
                ·
                  refine ⟨178296914622032223736445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1901833755968343719855413 178296914622032223736445)
                  ·
                    rfl

theorem cell21_781272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 5].length) (baseStart_781272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_781272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_781272 prefixEnd_781272 := by exact prefixLift 781272
  have htrace : WordTrace (prefixWord ++ tailWord_781272) baseStart_781272 baseEnd_781272 := by
    simpa [prefixWord, tailWord_781272, baseEnd_781272] using wordTrace_append hprefix tailTrace_781272
  have hstable : (prefixWord ++ tailWord_781272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781272).length < 2 ^ (prefixWord ++ tailWord_781272).sum := by decide
  have hdescent : baseEnd_781272 < baseStart_781272 := by decide
  rcases family_descends (prefixWord ++ tailWord_781272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781317 : List Nat := [1, 3, 1, 1, 2, 3, 4, 6]
def baseStart_781317 : Nat := 118140960795 + 781317 * 2 ^ 59
def prefixEnd_781317 : Nat := 4983230072969 + 3 ^ 40 * 781317 * 2
def baseEnd_781317 : Nat := 59435728078374048495451

theorem tailTrace_781317 : CollatzResearch.WordTrace tailWord_781317 prefixEnd_781317 59435728078374048495451 := by
  unfold tailWord_781317
  simp only [CollatzResearch.WordTrace]
  refine ⟨28496972110429422165142205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18997981406952948110094803 28496972110429422165142205)
  ·
    refine ⟨10686364541411033311928327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28496972110429422165142205 10686364541411033311928327)
    ·
      refine ⟨16029546812116549967892491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10686364541411033311928327 16029546812116549967892491)
      ·
        refine ⟨24044320218174824951838737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16029546812116549967892491 24044320218174824951838737)
        ·
          refine ⟨18033240163631118713879053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24044320218174824951838737 18033240163631118713879053)
          ·
            refine ⟨6762465061361669517704645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18033240163631118713879053 6762465061361669517704645)
            ·
              refine ⟨1267962199005313034569621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6762465061361669517704645 1267962199005313034569621)
              ·
                refine ⟨59435728078374048495451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1267962199005313034569621 59435728078374048495451)
                ·
                  rfl

theorem cell21_781317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 6].length) (baseStart_781317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_781317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_781317 prefixEnd_781317 := by exact prefixLift 781317
  have htrace : WordTrace (prefixWord ++ tailWord_781317) baseStart_781317 baseEnd_781317 := by
    simpa [prefixWord, tailWord_781317, baseEnd_781317] using wordTrace_append hprefix tailTrace_781317
  have hstable : (prefixWord ++ tailWord_781317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781317).length < 2 ^ (prefixWord ++ tailWord_781317).sum := by decide
  have hdescent : baseEnd_781317 < baseStart_781317 := by decide
  rcases family_descends (prefixWord ++ tailWord_781317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781320 : List Nat := [2, 1, 3, 2, 1, 3, 4, 1, 4]
def baseStart_781320 : Nat := 118140960795 + 781320 * 2 ^ 59
def prefixEnd_781320 : Nat := 4983230072969 + 3 ^ 40 * 781320 * 2
def baseEnd_781320 : Nat := 178307868875994806936347

theorem tailTrace_781320 : CollatzResearch.WordTrace tailWord_781320 prefixEnd_781320 178307868875994806936347 := by
  unfold tailWord_781320
  simp only [CollatzResearch.WordTrace]
  refine ⟨14248540764709276838750707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18998054352945702451667609 14248540764709276838750707)
  ·
    refine ⟨21372811147063915258126061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14248540764709276838750707 21372811147063915258126061)
    ·
      refine ⟨8014804180148968221797273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21372811147063915258126061 8014804180148968221797273)
      ·
        refine ⟨6011103135111726166347955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8014804180148968221797273 6011103135111726166347955)
        ·
          refine ⟨9016654702667589249521933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6011103135111726166347955 9016654702667589249521933)
          ·
            refine ⟨3381245513500345968570725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9016654702667589249521933 3381245513500345968570725)
            ·
              refine ⟨633983533781314869107011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3381245513500345968570725 633983533781314869107011)
              ·
                refine ⟨950975300671972303660517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 633983533781314869107011 950975300671972303660517)
                ·
                  refine ⟨178307868875994806936347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 950975300671972303660517 178307868875994806936347)
                  ·
                    rfl

theorem cell21_781320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 4].length) (baseStart_781320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_781320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_781320 prefixEnd_781320 := by exact prefixLift 781320
  have htrace : WordTrace (prefixWord ++ tailWord_781320) baseStart_781320 baseEnd_781320 := by
    simpa [prefixWord, tailWord_781320, baseEnd_781320] using wordTrace_append hprefix tailTrace_781320
  have hstable : (prefixWord ++ tailWord_781320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781320).length < 2 ^ (prefixWord ++ tailWord_781320).sum := by decide
  have hdescent : baseEnd_781320 < baseStart_781320 := by decide
  rcases family_descends (prefixWord ++ tailWord_781320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781331 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 7]
def baseStart_781331 : Nat := 118140960795 + 781331 * 2 ^ 59
def prefixEnd_781331 : Nat := 4983230072969 + 3 ^ 40 * 781331 * 2
def baseEnd_781331 : Nat := 178310379225861232252991

theorem tailTrace_781331 : CollatzResearch.WordTrace tailWord_781331 prefixEnd_781331 178310379225861232252991 := by
  unfold tailWord_781331
  simp only [CollatzResearch.WordTrace]
  refine ⟨28497482732378702556151847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18998321821585801704101231 28497482732378702556151847)
  ·
    refine ⟨42746224098568053834227771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28497482732378702556151847 42746224098568053834227771)
    ·
      refine ⟨64119336147852080751341657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42746224098568053834227771 64119336147852080751341657)
      ·
        refine ⟨48089502110889060563506243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64119336147852080751341657 48089502110889060563506243)
        ·
          refine ⟨72134253166333590845259365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48089502110889060563506243 72134253166333590845259365)
          ·
            refine ⟨13525172468687548283486131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72134253166333590845259365 13525172468687548283486131)
            ·
              refine ⟨20287758703031322425229197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13525172468687548283486131 20287758703031322425229197)
              ·
                refine ⟨7607909513636745909460949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20287758703031322425229197 7607909513636745909460949)
                ·
                  refine ⟨178310379225861232252991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7607909513636745909460949 178310379225861232252991)
                  ·
                    rfl

theorem cell21_781331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 7].length) (baseStart_781331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_781331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_781331 prefixEnd_781331 := by exact prefixLift 781331
  have htrace : WordTrace (prefixWord ++ tailWord_781331) baseStart_781331 baseEnd_781331 := by
    simpa [prefixWord, tailWord_781331, baseEnd_781331] using wordTrace_append hprefix tailTrace_781331
  have hstable : (prefixWord ++ tailWord_781331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781331).length < 2 ^ (prefixWord ++ tailWord_781331).sum := by decide
  have hdescent : baseEnd_781331 < baseStart_781331 := by decide
  rcases family_descends (prefixWord ++ tailWord_781331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781382 : List Nat := [6, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_781382 : Nat := 118140960795 + 781382 * 2 ^ 59
def prefixEnd_781382 : Nat := 4983230072969 + 3 ^ 40 * 781382 * 2
def baseEnd_781382 : Nat := 178322018120696476902887

theorem tailTrace_781382 : CollatzResearch.WordTrace tailWord_781382 prefixEnd_781382 178322018120696476902887 := by
  unfold tailWord_781382
  simp only [CollatzResearch.WordTrace]
  refine ⟨890604464224810570820575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18999561903462625510838933 890604464224810570820575)
  ·
    refine ⟨1335906696337215856230863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 890604464224810570820575 1335906696337215856230863)
    ·
      refine ⟨2003860044505823784346295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1335906696337215856230863 2003860044505823784346295)
      ·
        refine ⟨3005790066758735676519443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2003860044505823784346295 3005790066758735676519443)
        ·
          refine ⟨4508685100138103514779165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3005790066758735676519443 4508685100138103514779165)
          ·
            refine ⟨1690756912551788818042187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4508685100138103514779165 1690756912551788818042187)
            ·
              refine ⟨2536135368827683227063281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1690756912551788818042187 2536135368827683227063281)
              ·
                refine ⟨1902101526620762420297461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2536135368827683227063281 1902101526620762420297461)
                ·
                  refine ⟨178322018120696476902887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1902101526620762420297461 178322018120696476902887)
                  ·
                    rfl

theorem cell21_781382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_781382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_781382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_781382 prefixEnd_781382 := by exact prefixLift 781382
  have htrace : WordTrace (prefixWord ++ tailWord_781382) baseStart_781382 baseEnd_781382 := by
    simpa [prefixWord, tailWord_781382, baseEnd_781382] using wordTrace_append hprefix tailTrace_781382
  have hstable : (prefixWord ++ tailWord_781382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781382).length < 2 ^ (prefixWord ++ tailWord_781382).sum := by decide
  have hdescent : baseEnd_781382 < baseStart_781382 := by decide
  rcases family_descends (prefixWord ++ tailWord_781382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781407 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 7]
def baseStart_781407 : Nat := 118140960795 + 781407 * 2 ^ 59
def prefixEnd_781407 : Nat := 4983230072969 + 3 ^ 40 * 781407 * 2
def baseEnd_781407 : Nat := 178327723461301988986169

theorem tailTrace_781407 : CollatzResearch.WordTrace tailWord_781407 prefixEnd_781407 178327723461301988986169 := by
  unfold tailWord_781407
  simp only [CollatzResearch.WordTrace]
  refine ⟨28500254680103367535918475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19000169786735578357278983 28500254680103367535918475)
  ·
    refine ⟨42750382020155051303877713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28500254680103367535918475 42750382020155051303877713)
    ·
      refine ⟨32062786515116288477908285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42750382020155051303877713 32062786515116288477908285)
      ·
        refine ⟨12023544943168608179215607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32062786515116288477908285 12023544943168608179215607)
        ·
          refine ⟨18035317414752912268823411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12023544943168608179215607 18035317414752912268823411)
          ·
            refine ⟨27052976122129368403235117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18035317414752912268823411 27052976122129368403235117)
            ·
              refine ⟨10144866045798513151213169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27052976122129368403235117 10144866045798513151213169)
              ·
                refine ⟨7608649534348884863409877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10144866045798513151213169 7608649534348884863409877)
                ·
                  refine ⟨178327723461301988986169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7608649534348884863409877 178327723461301988986169)
                  ·
                    rfl

theorem cell21_781407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 7].length) (baseStart_781407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_781407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_781407 prefixEnd_781407 := by exact prefixLift 781407
  have htrace : WordTrace (prefixWord ++ tailWord_781407) baseStart_781407 baseEnd_781407 := by
    simpa [prefixWord, tailWord_781407, baseEnd_781407] using wordTrace_append hprefix tailTrace_781407
  have hstable : (prefixWord ++ tailWord_781407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781407).length < 2 ^ (prefixWord ++ tailWord_781407).sum := by decide
  have hdescent : baseEnd_781407 < baseStart_781407 := by decide
  rcases family_descends (prefixWord ++ tailWord_781407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781410 : List Nat := [3, 3, 2, 2, 1, 2, 8]
def baseStart_781410 : Nat := 118140960795 + 781410 * 2 ^ 59
def prefixEnd_781410 : Nat := 4983230072969 + 3 ^ 40 * 781410 * 2
def baseEnd_781410 : Nat := 19814267566908294492907

theorem tailTrace_781410 : CollatzResearch.WordTrace tailWord_781410 prefixEnd_781410 19814267566908294492907 := by
  unfold tailWord_781410
  simp only [CollatzResearch.WordTrace]
  refine ⟨7125091024773124762069421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19000242732728332698851789 7125091024773124762069421)
  ·
    refine ⟨2671909134289921785776033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7125091024773124762069421 2671909134289921785776033)
    ·
      refine ⟨2003931850717441339332025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2671909134289921785776033 2003931850717441339332025)
      ·
        refine ⟨1502948888038081004499019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2003931850717441339332025 1502948888038081004499019)
        ·
          refine ⟨2254423332057121506748529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1502948888038081004499019 2254423332057121506748529)
          ·
            refine ⟨1690817499042841130061397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2254423332057121506748529 1690817499042841130061397)
            ·
              refine ⟨19814267566908294492907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1690817499042841130061397 19814267566908294492907)
              ·
                rfl

theorem cell21_781410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 8].length) (baseStart_781410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_781410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_781410 prefixEnd_781410 := by exact prefixLift 781410
  have htrace : WordTrace (prefixWord ++ tailWord_781410) baseStart_781410 baseEnd_781410 := by
    simpa [prefixWord, tailWord_781410, baseEnd_781410] using wordTrace_append hprefix tailTrace_781410
  have hstable : (prefixWord ++ tailWord_781410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781410).length < 2 ^ (prefixWord ++ tailWord_781410).sum := by decide
  have hdescent : baseEnd_781410 < baseStart_781410 := by decide
  rcases family_descends (prefixWord ++ tailWord_781410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781424 : List Nat := [2, 1, 1, 1, 5, 1, 4, 1, 5]
def baseStart_781424 : Nat := 118140960795 + 781424 * 2 ^ 59
def prefixEnd_781424 : Nat := 4983230072969 + 3 ^ 40 * 781424 * 2
def baseEnd_781424 : Nat := 178331603092913737202801

theorem tailTrace_781424 : CollatzResearch.WordTrace tailWord_781424 prefixEnd_781424 178331603092913737202801 := by
  unfold tailWord_781424
  simp only [CollatzResearch.WordTrace]
  refine ⟨14250437360520889719643663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19000583147361186292858217 14250437360520889719643663)
  ·
    refine ⟨21375656040781334579465495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14250437360520889719643663 21375656040781334579465495)
    ·
      refine ⟨32063484061172001869198243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21375656040781334579465495 32063484061172001869198243)
      ·
        refine ⟨48095226091758002803797365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32063484061172001869198243 48095226091758002803797365)
        ·
          refine ⟨4508927446102312762856003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48095226091758002803797365 4508927446102312762856003)
          ·
            refine ⟨6763391169153469144284005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4508927446102312762856003 6763391169153469144284005)
            ·
              refine ⟨1268135844216275464553251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6763391169153469144284005 1268135844216275464553251)
              ·
                refine ⟨1902203766324413196829877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1268135844216275464553251 1902203766324413196829877)
                ·
                  refine ⟨178331603092913737202801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1902203766324413196829877 178331603092913737202801)
                  ·
                    rfl

theorem cell21_781424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 5].length) (baseStart_781424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_781424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_781424 prefixEnd_781424 := by exact prefixLift 781424
  have htrace : WordTrace (prefixWord ++ tailWord_781424) baseStart_781424 baseEnd_781424 := by
    simpa [prefixWord, tailWord_781424, baseEnd_781424] using wordTrace_append hprefix tailTrace_781424
  have hstable : (prefixWord ++ tailWord_781424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781424).length < 2 ^ (prefixWord ++ tailWord_781424).sum := by decide
  have hdescent : baseEnd_781424 < baseStart_781424 := by decide
  rcases family_descends (prefixWord ++ tailWord_781424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781458 : List Nat := [3, 2, 3, 1, 1, 2, 3, 3, 3]
def baseStart_781458 : Nat := 118140960795 + 781458 * 2 ^ 59
def prefixEnd_781458 : Nat := 4983230072969 + 3 ^ 40 * 781458 * 2
def baseEnd_781458 : Nat := 178339362356137233636065

theorem tailTrace_781458 : CollatzResearch.WordTrace tailWord_781458 prefixEnd_781458 178339362356137233636065 := by
  unfold tailWord_781458
  simp only [CollatzResearch.WordTrace]
  refine ⟨7125528700729650811506257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19001409868612402164016685 7125528700729650811506257)
  ·
    refine ⟨5344146525547238108629693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7125528700729650811506257 5344146525547238108629693)
    ·
      refine ⟨2004054947080214290736135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5344146525547238108629693 2004054947080214290736135)
      ·
        refine ⟨3006082420620321436104203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2004054947080214290736135 3006082420620321436104203)
        ·
          refine ⟨4509123630930482154156305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3006082420620321436104203 4509123630930482154156305)
          ·
            refine ⟨3381842723197861615617229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4509123630930482154156305 3381842723197861615617229)
            ·
              refine ⟨1268191021199198105856461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3381842723197861615617229 1268191021199198105856461)
              ·
                refine ⟨475571632949699289696173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1268191021199198105856461 475571632949699289696173)
                ·
                  refine ⟨178339362356137233636065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 475571632949699289696173 178339362356137233636065)
                  ·
                    rfl

theorem cell21_781458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_781458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_781458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_781458 prefixEnd_781458 := by exact prefixLift 781458
  have htrace : WordTrace (prefixWord ++ tailWord_781458) baseStart_781458 baseEnd_781458 := by
    simpa [prefixWord, tailWord_781458, baseEnd_781458] using wordTrace_append hprefix tailTrace_781458
  have hstable : (prefixWord ++ tailWord_781458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781458).length < 2 ^ (prefixWord ++ tailWord_781458).sum := by decide
  have hdescent : baseEnd_781458 < baseStart_781458 := by decide
  rcases family_descends (prefixWord ++ tailWord_781458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781489 : List Nat := [1, 2, 2, 5, 1, 3, 2, 1, 4]
def baseStart_781489 : Nat := 118140960795 + 781489 * 2 ^ 59
def prefixEnd_781489 : Nat := 4983230072969 + 3 ^ 40 * 781489 * 2
def baseEnd_781489 : Nat := 178346436978488068619335

theorem tailTrace_781489 : CollatzResearch.WordTrace tailWord_781489 prefixEnd_781489 178346436978488068619335 := by
  unfold tailWord_781489
  simp only [CollatzResearch.WordTrace]
  refine ⟨28503245465806295540403521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19002163643870863693602347 28503245465806295540403521)
  ·
    refine ⟨21377434099354721655302641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28503245465806295540403521 21377434099354721655302641)
    ·
      refine ⟨16033075574516041241476981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21377434099354721655302641 16033075574516041241476981)
      ·
        refine ⟨1503100835110878866388467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16033075574516041241476981 1503100835110878866388467)
        ·
          refine ⟨2254651252666318299582701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1503100835110878866388467 2254651252666318299582701)
          ·
            refine ⟨845494219749869362343513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2254651252666318299582701 845494219749869362343513)
            ·
              refine ⟨634120664812402021757635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 845494219749869362343513 634120664812402021757635)
              ·
                refine ⟨951180997218603032636453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 634120664812402021757635 951180997218603032636453)
                ·
                  refine ⟨178346436978488068619335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 951180997218603032636453 178346436978488068619335)
                  ·
                    rfl

theorem cell21_781489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 4].length) (baseStart_781489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_781489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_781489 prefixEnd_781489 := by exact prefixLift 781489
  have htrace : WordTrace (prefixWord ++ tailWord_781489) baseStart_781489 baseEnd_781489 := by
    simpa [prefixWord, tailWord_781489, baseEnd_781489] using wordTrace_append hprefix tailTrace_781489
  have hstable : (prefixWord ++ tailWord_781489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781489).length < 2 ^ (prefixWord ++ tailWord_781489).sum := by decide
  have hdescent : baseEnd_781489 < baseStart_781489 := by decide
  rcases family_descends (prefixWord ++ tailWord_781489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781528 : List Nat := [2, 1, 2, 2, 14]
def baseStart_781528 : Nat := 118140960795 + 781528 * 2 ^ 59
def prefixEnd_781528 : Nat := 4983230072969 + 3 ^ 40 * 781528 * 2
def baseEnd_781528 : Nat := 2201917744565835400855

theorem tailTrace_781528 : CollatzResearch.WordTrace tailWord_781528 prefixEnd_781528 2201917744565835400855 := by
  unfold tailWord_781528
  simp only [CollatzResearch.WordTrace]
  refine ⟨14252333956332502600536619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19003111941776670134048825 14252333956332502600536619)
  ·
    refine ⟨21378500934498753900804929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14252333956332502600536619 21378500934498753900804929)
    ·
      refine ⟨16033875700874065425603697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21378500934498753900804929 16033875700874065425603697)
      ·
        refine ⟨12025406775655549069202773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16033875700874065425603697 12025406775655549069202773)
        ·
          refine ⟨2201917744565835400855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 12025406775655549069202773 2201917744565835400855)
          ·
            rfl

theorem cell21_781528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 14].length) (baseStart_781528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_781528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_781528 prefixEnd_781528 := by exact prefixLift 781528
  have htrace : WordTrace (prefixWord ++ tailWord_781528) baseStart_781528 baseEnd_781528 := by
    simpa [prefixWord, tailWord_781528, baseEnd_781528] using wordTrace_append hprefix tailTrace_781528
  have hstable : (prefixWord ++ tailWord_781528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781528).length < 2 ^ (prefixWord ++ tailWord_781528).sum := by decide
  have hdescent : baseEnd_781528 < baseStart_781528 := by decide
  rcases family_descends (prefixWord ++ tailWord_781528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781559 : List Nat := [1, 1, 3, 1, 1, 1, 2, 6, 5]
def baseStart_781559 : Nat := 118140960795 + 781559 * 2 ^ 59
def prefixEnd_781559 : Nat := 4983230072969 + 3 ^ 40 * 781559 * 2
def baseEnd_781559 : Nat := 178362411932183502452525

theorem tailTrace_781559 : CollatzResearch.WordTrace tailWord_781559 prefixEnd_781559 178362411932183502452525 := by
  unfold tailWord_781559
  simp only [CollatzResearch.WordTrace]
  refine ⟨28505798575552697495451731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19003865717035131663634487 28505798575552697495451731)
  ·
    refine ⟨42758697863329046243177597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28505798575552697495451731 42758697863329046243177597)
    ·
      refine ⟨16034511698748392341191599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42758697863329046243177597 16034511698748392341191599)
      ·
        refine ⟨24051767548122588511787399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16034511698748392341191599 24051767548122588511787399)
        ·
          refine ⟨36077651322183882767681099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24051767548122588511787399 36077651322183882767681099)
          ·
            refine ⟨54116476983275824151521649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36077651322183882767681099 54116476983275824151521649)
            ·
              refine ⟨40587357737456868113641237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54116476983275824151521649 40587357737456868113641237)
              ·
                refine ⟨1902532393943290692826933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40587357737456868113641237 1902532393943290692826933)
                ·
                  refine ⟨178362411932183502452525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1902532393943290692826933 178362411932183502452525)
                  ·
                    rfl

theorem cell21_781559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 5].length) (baseStart_781559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_781559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_781559 prefixEnd_781559 := by exact prefixLift 781559
  have htrace : WordTrace (prefixWord ++ tailWord_781559) baseStart_781559 baseEnd_781559 := by
    simpa [prefixWord, tailWord_781559, baseEnd_781559] using wordTrace_append hprefix tailTrace_781559
  have hstable : (prefixWord ++ tailWord_781559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781559).length < 2 ^ (prefixWord ++ tailWord_781559).sum := by decide
  have hdescent : baseEnd_781559 < baseStart_781559 := by decide
  rcases family_descends (prefixWord ++ tailWord_781559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781621 : List Nat := [1, 3, 3, 1, 2, 3, 1, 7]
def baseStart_781621 : Nat := 118140960795 + 781621 * 2 ^ 59
def prefixEnd_781621 : Nat := 4983230072969 + 3 ^ 40 * 781621 * 2
def baseEnd_781621 : Nat := 59458853725628390806355

theorem tailTrace_781621 : CollatzResearch.WordTrace tailWord_781621 prefixEnd_781621 59458853725628390806355 := by
  unfold tailWord_781621
  simp only [CollatzResearch.WordTrace]
  refine ⟨28508059901328082084208717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19005373267552054722805811 28508059901328082084208717)
  ·
    refine ⟨10690522462998030781578269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28508059901328082084208717 10690522462998030781578269)
    ·
      refine ⟨4008945923624261543091851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10690522462998030781578269 4008945923624261543091851)
      ·
        refine ⟨6013418885436392314637777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4008945923624261543091851 6013418885436392314637777)
        ·
          refine ⟨4510064164077294235978333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6013418885436392314637777 4510064164077294235978333)
          ·
            refine ⟨1691274061528985338491875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4510064164077294235978333 1691274061528985338491875)
            ·
              refine ⟨2536911092293478007737813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1691274061528985338491875 2536911092293478007737813)
              ·
                refine ⟨59458853725628390806355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2536911092293478007737813 59458853725628390806355)
                ·
                  rfl

theorem cell21_781621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 7].length) (baseStart_781621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_781621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_781621 prefixEnd_781621 := by exact prefixLift 781621
  have htrace : WordTrace (prefixWord ++ tailWord_781621) baseStart_781621 baseEnd_781621 := by
    simpa [prefixWord, tailWord_781621, baseEnd_781621] using wordTrace_append hprefix tailTrace_781621
  have hstable : (prefixWord ++ tailWord_781621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781621).length < 2 ^ (prefixWord ++ tailWord_781621).sum := by decide
  have hdescent : baseEnd_781621 < baseStart_781621 := by decide
  rcases family_descends (prefixWord ++ tailWord_781621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781680 : List Nat := [2, 1, 1, 1, 4, 2, 1, 9]
def baseStart_781680 : Nat := 118140960795 + 781680 * 2 ^ 59
def prefixEnd_781680 : Nat := 4983230072969 + 3 ^ 40 * 781680 * 2
def baseEnd_781680 : Nat := 59463341926904726978537

theorem tailTrace_781680 : CollatzResearch.WordTrace tailWord_781680 prefixEnd_781680 59463341926904726978537 := by
  unfold tailWord_781680
  simp only [CollatzResearch.WordTrace]
  refine ⟨14255105904057167580303247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19006807872076223440404329 14255105904057167580303247)
  ·
    refine ⟨21382658856085751370454871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14255105904057167580303247 21382658856085751370454871)
    ·
      refine ⟨32073988284128627055682307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21382658856085751370454871 32073988284128627055682307)
      ·
        refine ⟨48110982426192940583523461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32073988284128627055682307 48110982426192940583523461)
        ·
          refine ⟨9020809204911176359410649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48110982426192940583523461 9020809204911176359410649)
          ·
            refine ⟨6765606903683382269557987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9020809204911176359410649 6765606903683382269557987)
            ·
              refine ⟨10148410355525073404336981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6765606903683382269557987 10148410355525073404336981)
              ·
                refine ⟨59463341926904726978537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10148410355525073404336981 59463341926904726978537)
                ·
                  rfl

theorem cell21_781680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 9].length) (baseStart_781680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_781680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_781680 prefixEnd_781680 := by exact prefixLift 781680
  have htrace : WordTrace (prefixWord ++ tailWord_781680) baseStart_781680 baseEnd_781680 := by
    simpa [prefixWord, tailWord_781680, baseEnd_781680] using wordTrace_append hprefix tailTrace_781680
  have hstable : (prefixWord ++ tailWord_781680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781680).length < 2 ^ (prefixWord ++ tailWord_781680).sum := by decide
  have hdescent : baseEnd_781680 < baseStart_781680 := by decide
  rcases family_descends (prefixWord ++ tailWord_781680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781697 : List Nat := [1, 2, 4, 3, 2, 9]
def baseStart_781697 : Nat := 118140960795 + 781697 * 2 ^ 59
def prefixEnd_781697 : Nat := 4983230072969 + 3 ^ 40 * 781697 * 2
def baseEnd_781697 : Nat := 6607181681937997376009

theorem tailTrace_781697 : CollatzResearch.WordTrace tailWord_781697 prefixEnd_781697 6607181681937997376009 := by
  unfold tailWord_781697
  simp only [CollatzResearch.WordTrace]
  refine ⟨28510831849052747063975345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19007221232701831375983563 28510831849052747063975345)
  ·
    refine ⟨21383123886789560297981509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28510831849052747063975345 21383123886789560297981509)
    ·
      refine ⟨4009335728773042555871533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21383123886789560297981509 4009335728773042555871533)
      ·
        refine ⟨1503500898289890958451825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4009335728773042555871533 1503500898289890958451825)
        ·
          refine ⟨1127625673717418218838869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1503500898289890958451825 1127625673717418218838869)
          ·
            refine ⟨6607181681937997376009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1127625673717418218838869 6607181681937997376009)
            ·
              rfl

theorem cell21_781697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 9].length) (baseStart_781697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_781697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_781697 prefixEnd_781697 := by exact prefixLift 781697
  have htrace : WordTrace (prefixWord ++ tailWord_781697) baseStart_781697 baseEnd_781697 := by
    simpa [prefixWord, tailWord_781697, baseEnd_781697] using wordTrace_append hprefix tailTrace_781697
  have hstable : (prefixWord ++ tailWord_781697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781697).length < 2 ^ (prefixWord ++ tailWord_781697).sum := by decide
  have hdescent : baseEnd_781697 < baseStart_781697 := by decide
  rcases family_descends (prefixWord ++ tailWord_781697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781745 : List Nat := [1, 2, 2, 4, 1, 1, 4, 3, 3]
def baseStart_781745 : Nat := 118140960795 + 781745 * 2 ^ 59
def prefixEnd_781745 : Nat := 4983230072969 + 3 ^ 40 * 781745 * 2
def baseEnd_781745 : Nat := 178404859666288512352145

theorem tailTrace_781745 : CollatzResearch.WordTrace tailWord_781745 prefixEnd_781745 178404859666288512352145 := by
  unfold tailWord_781745
  simp only [CollatzResearch.WordTrace]
  refine ⟨28512582552878851261722689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19008388368585900841148459 28512582552878851261722689)
  ·
    refine ⟨21384436914659138446292017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28512582552878851261722689 21384436914659138446292017)
    ·
      refine ⟨16038327685994353834719013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21384436914659138446292017 16038327685994353834719013)
      ·
        refine ⟨3007186441123941344009815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16038327685994353834719013 3007186441123941344009815)
        ·
          refine ⟨4510779661685912016014723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3007186441123941344009815 4510779661685912016014723)
          ·
            refine ⟨6766169492528868024022085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4510779661685912016014723 6766169492528868024022085)
            ·
              refine ⟨1268656779849162754504141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6766169492528868024022085 1268656779849162754504141)
              ·
                refine ⟨475746292443436032939053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1268656779849162754504141 475746292443436032939053)
                ·
                  refine ⟨178404859666288512352145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 475746292443436032939053 178404859666288512352145)
                  ·
                    rfl

theorem cell21_781745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 3, 3].length) (baseStart_781745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_781745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_781745 prefixEnd_781745 := by exact prefixLift 781745
  have htrace : WordTrace (prefixWord ++ tailWord_781745) baseStart_781745 baseEnd_781745 := by
    simpa [prefixWord, tailWord_781745, baseEnd_781745] using wordTrace_append hprefix tailTrace_781745
  have hstable : (prefixWord ++ tailWord_781745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781745).length < 2 ^ (prefixWord ++ tailWord_781745).sum := by decide
  have hdescent : baseEnd_781745 < baseStart_781745 := by decide
  rcases family_descends (prefixWord ++ tailWord_781745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781804 : List Nat := [2, 2, 1, 1, 2, 1, 2, 7, 3]
def baseStart_781804 : Nat := 118140960795 + 781804 * 2 ^ 59
def prefixEnd_781804 : Nat := 4983230072969 + 3 ^ 40 * 781804 * 2
def baseEnd_781804 : Nat := 178418324270117520868691

theorem tailTrace_781804 : CollatzResearch.WordTrace tailWord_781804 prefixEnd_781804 178418324270117520868691 := by
  unfold tailWord_781804
  simp only [CollatzResearch.WordTrace]
  refine ⟨14257367229832552169060233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19009822973110069558746977 14257367229832552169060233)
  ·
    refine ⟨10693025422374414126795175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14257367229832552169060233 10693025422374414126795175)
    ·
      refine ⟨16039538133561621190192763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10693025422374414126795175 16039538133561621190192763)
      ·
        refine ⟨24059307200342431785289145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16039538133561621190192763 24059307200342431785289145)
        ·
          refine ⟨18044480400256823838966859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24059307200342431785289145 18044480400256823838966859)
          ·
            refine ⟨27066720600385235758450289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18044480400256823838966859 27066720600385235758450289)
            ·
              refine ⟨20300040450288926818837717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27066720600385235758450289 20300040450288926818837717)
              ·
                refine ⟨475782198053646722316509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 20300040450288926818837717 475782198053646722316509)
                ·
                  refine ⟨178418324270117520868691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 475782198053646722316509 178418324270117520868691)
                  ·
                    rfl

theorem cell21_781804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7, 3].length) (baseStart_781804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_781804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_781804 prefixEnd_781804 := by exact prefixLift 781804
  have htrace : WordTrace (prefixWord ++ tailWord_781804) baseStart_781804 baseEnd_781804 := by
    simpa [prefixWord, tailWord_781804, baseEnd_781804] using wordTrace_append hprefix tailTrace_781804
  have hstable : (prefixWord ++ tailWord_781804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781804).length < 2 ^ (prefixWord ++ tailWord_781804).sum := by decide
  have hdescent : baseEnd_781804 < baseStart_781804 := by decide
  rcases family_descends (prefixWord ++ tailWord_781804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781818 : List Nat := [3, 1, 1, 1, 1, 2, 4, 4, 4]
def baseStart_781818 : Nat := 118140960795 + 781818 * 2 ^ 59
def prefixEnd_781818 : Nat := 4983230072969 + 3 ^ 40 * 781818 * 2
def baseEnd_781818 : Nat := 178421519260856607635329

theorem tailTrace_781818 : CollatzResearch.WordTrace tailWord_781818 prefixEnd_781818 178421519260856607635329 := by
  unfold tailWord_781818
  simp only [CollatzResearch.WordTrace]
  refine ⟨7128811270403596182282527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19010163387742923152753405 7128811270403596182282527)
  ·
    refine ⟨10693216905605394273423791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7128811270403596182282527 10693216905605394273423791)
    ·
      refine ⟨16039825358408091410135687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10693216905605394273423791 16039825358408091410135687)
      ·
        refine ⟨24059738037612137115203531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16039825358408091410135687 24059738037612137115203531)
        ·
          refine ⟨36089607056418205672805297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24059738037612137115203531 36089607056418205672805297)
          ·
            refine ⟨27067205292313654254603973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36089607056418205672805297 27067205292313654254603973)
            ·
              refine ⟨5075100992308810172738245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27067205292313654254603973 5075100992308810172738245)
              ·
                refine ⟨951581436057901907388421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5075100992308810172738245 951581436057901907388421)
                ·
                  refine ⟨178421519260856607635329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 951581436057901907388421 178421519260856607635329)
                  ·
                    rfl

theorem cell21_781818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_781818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_781818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_781818 prefixEnd_781818 := by exact prefixLift 781818
  have htrace : WordTrace (prefixWord ++ tailWord_781818) baseStart_781818 baseEnd_781818 := by
    simpa [prefixWord, tailWord_781818, baseEnd_781818] using wordTrace_append hprefix tailTrace_781818
  have hstable : (prefixWord ++ tailWord_781818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781818).length < 2 ^ (prefixWord ++ tailWord_781818).sum := by decide
  have hdescent : baseEnd_781818 < baseStart_781818 := by decide
  rcases family_descends (prefixWord ++ tailWord_781818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781832 : List Nat := [2, 1, 3, 2, 1, 1, 3, 8]
def baseStart_781832 : Nat := 118140960795 + 781832 * 2 ^ 59
def prefixEnd_781832 : Nat := 4983230072969 + 3 ^ 40 * 781832 * 2
def baseEnd_781832 : Nat := 59474904750531898133989

theorem tailTrace_781832 : CollatzResearch.WordTrace tailWord_781832 prefixEnd_781832 59474904750531898133989 := by
  unfold tailWord_781832
  simp only [CollatzResearch.WordTrace]
  refine ⟨14257877851781832560069875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19010503802375776746759833 14257877851781832560069875)
  ·
    refine ⟨21386816777672748840104813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14257877851781832560069875 21386816777672748840104813)
    ·
      refine ⟨8020056291627280815039305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21386816777672748840104813 8020056291627280815039305)
      ·
        refine ⟨6015042218720460611279479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8020056291627280815039305 6015042218720460611279479)
        ·
          refine ⟨9022563328080690916919219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6015042218720460611279479 9022563328080690916919219)
          ·
            refine ⟨13533844992121036375378829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9022563328080690916919219 13533844992121036375378829)
            ·
              refine ⟨5075191872045388640767061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13533844992121036375378829 5075191872045388640767061)
              ·
                refine ⟨59474904750531898133989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5075191872045388640767061 59474904750531898133989)
                ·
                  rfl

theorem cell21_781832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 8].length) (baseStart_781832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_781832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_781832 prefixEnd_781832 := by exact prefixLift 781832
  have htrace : WordTrace (prefixWord ++ tailWord_781832) baseStart_781832 baseEnd_781832 := by
    simpa [prefixWord, tailWord_781832, baseEnd_781832] using wordTrace_append hprefix tailTrace_781832
  have hstable : (prefixWord ++ tailWord_781832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781832).length < 2 ^ (prefixWord ++ tailWord_781832).sum := by decide
  have hdescent : baseEnd_781832 < baseStart_781832 := by decide
  rcases family_descends (prefixWord ++ tailWord_781832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781835 : List Nat := [1, 1, 1, 1, 8, 1, 1, 3, 4]
def baseStart_781835 : Nat := 118140960795 + 781835 * 2 ^ 59
def prefixEnd_781835 : Nat := 4983230072969 + 3 ^ 40 * 781835 * 2
def baseEnd_781835 : Nat := 178425398892468355851961

theorem tailTrace_781835 : CollatzResearch.WordTrace tailWord_781835 prefixEnd_781835 178425398892468355851961 := by
  unfold tailWord_781835
  simp only [CollatzResearch.WordTrace]
  refine ⟨28515865122552796632498959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19010576748368531088332639 28515865122552796632498959)
  ·
    refine ⟨42773797683829194948748439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28515865122552796632498959 42773797683829194948748439)
    ·
      refine ⟨64160696525743792423122659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42773797683829194948748439 64160696525743792423122659)
      ·
        refine ⟨96241044788615688634683989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64160696525743792423122659 96241044788615688634683989)
        ·
          refine ⟨1127824743616590101187703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 96241044788615688634683989 1127824743616590101187703)
          ·
            refine ⟨1691737115424885151781555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1127824743616590101187703 1691737115424885151781555)
            ·
              refine ⟨2537605673137327727672333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1691737115424885151781555 2537605673137327727672333)
              ·
                refine ⟨951602127426497897877125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2537605673137327727672333 951602127426497897877125)
                ·
                  refine ⟨178425398892468355851961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 951602127426497897877125 178425398892468355851961)
                  ·
                    rfl

theorem cell21_781835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 4].length) (baseStart_781835 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_781835 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_781835 prefixEnd_781835 := by exact prefixLift 781835
  have htrace : WordTrace (prefixWord ++ tailWord_781835) baseStart_781835 baseEnd_781835 := by
    simpa [prefixWord, tailWord_781835, baseEnd_781835] using wordTrace_append hprefix tailTrace_781835
  have hstable : (prefixWord ++ tailWord_781835).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781835).length < 2 ^ (prefixWord ++ tailWord_781835).sum := by decide
  have hdescent : baseEnd_781835 < baseStart_781835 := by decide
  rcases family_descends (prefixWord ++ tailWord_781835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781928 : List Nat := [2, 1, 4, 3, 1, 3, 1, 2, 4]
def baseStart_781928 : Nat := 118140960795 + 781928 * 2 ^ 59
def prefixEnd_781928 : Nat := 4983230072969 + 3 ^ 40 * 781928 * 2
def baseEnd_781928 : Nat := 178446622759520860801771

theorem tailTrace_781928 : CollatzResearch.WordTrace tailWord_781928 prefixEnd_781928 178446622759520860801771 := by
  unfold tailWord_781928
  simp only [CollatzResearch.WordTrace]
  refine ⟨14259628555607936757817219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19012838074143915677089625 14259628555607936757817219)
  ·
    refine ⟨21389442833411905136725829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14259628555607936757817219 21389442833411905136725829)
    ·
      refine ⟨4010520531264732213136093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21389442833411905136725829 4010520531264732213136093)
      ·
        refine ⟨1503945199224274579926035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4010520531264732213136093 1503945199224274579926035)
        ·
          refine ⟨2255917798836411869889053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1503945199224274579926035 2255917798836411869889053)
          ·
            refine ⟨845969174563654451208395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2255917798836411869889053 845969174563654451208395)
            ·
              refine ⟨1268953761845481676812593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 845969174563654451208395 1268953761845481676812593)
              ·
                refine ⟨951715321384111257609445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1268953761845481676812593 951715321384111257609445)
                ·
                  refine ⟨178446622759520860801771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 951715321384111257609445 178446622759520860801771)
                  ·
                    rfl

theorem cell21_781928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 4].length) (baseStart_781928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_781928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_781928 prefixEnd_781928 := by exact prefixLift 781928
  have htrace : WordTrace (prefixWord ++ tailWord_781928) baseStart_781928 baseEnd_781928 := by
    simpa [prefixWord, tailWord_781928, baseEnd_781928] using wordTrace_append hprefix tailTrace_781928
  have hstable : (prefixWord ++ tailWord_781928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781928).length < 2 ^ (prefixWord ++ tailWord_781928).sum := by decide
  have hdescent : baseEnd_781928 < baseStart_781928 := by decide
  rcases family_descends (prefixWord ++ tailWord_781928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781984 : List Nat := [2, 1, 1, 4, 3, 1, 9]
def baseStart_781984 : Nat := 118140960795 + 781984 * 2 ^ 59
def prefixEnd_781984 : Nat := 4983230072969 + 3 ^ 40 * 781984 * 2
def baseEnd_781984 : Nat := 19828822524719689763147

theorem tailTrace_781984 : CollatzResearch.WordTrace tailWord_781984 prefixEnd_781984 19828822524719689763147 := by
  unfold tailWord_781984
  simp only [CollatzResearch.WordTrace]
  refine ⟨14260649799506497539836503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19014199732675330053115337 14260649799506497539836503)
  ·
    refine ⟨21390974699259746309754755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14260649799506497539836503 21390974699259746309754755)
    ·
      refine ⟨32086462048889619464632133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21390974699259746309754755 32086462048889619464632133)
      ·
        refine ⟨6016211634166803649618525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32086462048889619464632133 6016211634166803649618525)
        ·
          refine ⟨2256079362812551368606947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6016211634166803649618525 2256079362812551368606947)
          ·
            refine ⟨3384119044218827052910421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2256079362812551368606947 3384119044218827052910421)
            ·
              refine ⟨19828822524719689763147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3384119044218827052910421 19828822524719689763147)
              ·
                rfl

theorem cell21_781984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 9].length) (baseStart_781984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_781984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_781984 prefixEnd_781984 := by exact prefixLift 781984
  have htrace : WordTrace (prefixWord ++ tailWord_781984) baseStart_781984 baseEnd_781984 := by
    simpa [prefixWord, tailWord_781984, baseEnd_781984] using wordTrace_append hprefix tailTrace_781984
  have hstable : (prefixWord ++ tailWord_781984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781984).length < 2 ^ (prefixWord ++ tailWord_781984).sum := by decide
  have hdescent : baseEnd_781984 < baseStart_781984 := by decide
  rcases family_descends (prefixWord ++ tailWord_781984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782049 : List Nat := [1, 2, 3, 1, 5, 1, 1, 4, 3]
def baseStart_782049 : Nat := 118140960795 + 782049 * 2 ^ 59
def prefixEnd_782049 : Nat := 4983230072969 + 3 ^ 40 * 782049 * 2
def baseEnd_782049 : Nat := 178474236608051539284857

theorem tailTrace_782049 : CollatzResearch.WordTrace tailWord_782049 prefixEnd_782049 178474236608051539284857 := by
  unfold tailWord_782049
  simp only [CollatzResearch.WordTrace]
  refine ⟨28523670343777511180789201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19015780229185007453859467 28523670343777511180789201)
  ·
    refine ⟨21392752757833133385591901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28523670343777511180789201 21392752757833133385591901)
    ·
      refine ⟨8022282284187425019596963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21392752757833133385591901 8022282284187425019596963)
      ·
        refine ⟨12033423426281137529395445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8022282284187425019596963 12033423426281137529395445)
        ·
          refine ⟨1128133446213856643380823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12033423426281137529395445 1128133446213856643380823)
          ·
            refine ⟨1692200169320784965071235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1128133446213856643380823 1692200169320784965071235)
            ·
              refine ⟨2538300253981177447606853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1692200169320784965071235 2538300253981177447606853)
              ·
                refine ⟨475931297621470771426285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2538300253981177447606853 475931297621470771426285)
                ·
                  refine ⟨178474236608051539284857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 475931297621470771426285 178474236608051539284857)
                  ·
                    rfl

theorem cell21_782049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 4, 3].length) (baseStart_782049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_782049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_782049 prefixEnd_782049 := by exact prefixLift 782049
  have htrace : WordTrace (prefixWord ++ tailWord_782049) baseStart_782049 baseEnd_782049 := by
    simpa [prefixWord, tailWord_782049, baseEnd_782049] using wordTrace_append hprefix tailTrace_782049
  have hstable : (prefixWord ++ tailWord_782049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782049).length < 2 ^ (prefixWord ++ tailWord_782049).sum := by decide
  have hdescent : baseEnd_782049 < baseStart_782049 := by decide
  rcases family_descends (prefixWord ++ tailWord_782049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782060 : List Nat := [2, 2, 1, 1, 2, 2, 5, 6]
def baseStart_782060 : Nat := 118140960795 + 782060 * 2 ^ 59
def prefixEnd_782060 : Nat := 4983230072969 + 3 ^ 40 * 782060 * 2
def baseEnd_782060 : Nat := 59492248985972654867167

theorem tailTrace_782060 : CollatzResearch.WordTrace tailWord_782060 prefixEnd_782060 59492248985972654867167 := by
  unfold tailWord_782060
  simp only [CollatzResearch.WordTrace]
  refine ⟨14262035773368830029719817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19016047697825106706293089 14262035773368830029719817)
  ·
    refine ⟨10696526830026622522289863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14262035773368830029719817 10696526830026622522289863)
    ·
      refine ⟨16044790245039933783434795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10696526830026622522289863 16044790245039933783434795)
      ·
        refine ⟨24067185367559900675152193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16044790245039933783434795 24067185367559900675152193)
        ·
          refine ⟨18050389025669925506364145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24067185367559900675152193 18050389025669925506364145)
          ·
            refine ⟨13537791769252444129773109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18050389025669925506364145 13537791769252444129773109)
            ·
              refine ⟨1269167978367416637166229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13537791769252444129773109 1269167978367416637166229)
              ·
                refine ⟨59492248985972654867167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1269167978367416637166229 59492248985972654867167)
                ·
                  rfl

theorem cell21_782060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 6].length) (baseStart_782060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_782060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_782060 prefixEnd_782060 := by exact prefixLift 782060
  have htrace : WordTrace (prefixWord ++ tailWord_782060) baseStart_782060 baseEnd_782060 := by
    simpa [prefixWord, tailWord_782060, baseEnd_782060] using wordTrace_append hprefix tailTrace_782060
  have hstable : (prefixWord ++ tailWord_782060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782060).length < 2 ^ (prefixWord ++ tailWord_782060).sum := by decide
  have hdescent : baseEnd_782060 < baseStart_782060 := by decide
  rcases family_descends (prefixWord ++ tailWord_782060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782108 : List Nat := [2, 2, 3, 1, 1, 2, 1, 6, 3]
def baseStart_782108 : Nat := 118140960795 + 782108 * 2 ^ 59
def prefixEnd_782108 : Nat := 4983230072969 + 3 ^ 40 * 782108 * 2
def baseEnd_782108 : Nat := 178487701211880547801403

theorem tailTrace_782108 : CollatzResearch.WordTrace tailWord_782108 prefixEnd_782108 178487701211880547801403 := by
  unfold tailWord_782108
  simp only [CollatzResearch.WordTrace]
  refine ⟨14262911125281882128593489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19017214833709176171457985 14262911125281882128593489)
  ·
    refine ⟨10697183343961411596445117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14262911125281882128593489 10697183343961411596445117)
    ·
      refine ⟨4011443753985529348666919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10697183343961411596445117 4011443753985529348666919)
      ·
        refine ⟨6017165630978294023000379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4011443753985529348666919 6017165630978294023000379)
        ·
          refine ⟨9025748446467441034500569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6017165630978294023000379 9025748446467441034500569)
          ·
            refine ⟨6769311334850580775875427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9025748446467441034500569 6769311334850580775875427)
            ·
              refine ⟨10153967002275871163813141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6769311334850580775875427 10153967002275871163813141)
              ·
                refine ⟨475967203231681460803741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10153967002275871163813141 475967203231681460803741)
                ·
                  refine ⟨178487701211880547801403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 475967203231681460803741 178487701211880547801403)
                  ·
                    rfl

theorem cell21_782108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 6, 3].length) (baseStart_782108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_782108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_782108 prefixEnd_782108 := by exact prefixLift 782108
  have htrace : WordTrace (prefixWord ++ tailWord_782108) baseStart_782108 baseEnd_782108 := by
    simpa [prefixWord, tailWord_782108, baseEnd_782108] using wordTrace_append hprefix tailTrace_782108
  have hstable : (prefixWord ++ tailWord_782108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782108).length < 2 ^ (prefixWord ++ tailWord_782108).sum := by decide
  have hdescent : baseEnd_782108 < baseStart_782108 := by decide
  rcases family_descends (prefixWord ++ tailWord_782108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782136 : List Nat := [2, 1, 2, 1, 3, 4, 1, 7]
def baseStart_782136 : Nat := 118140960795 + 782136 * 2 ^ 59
def prefixEnd_782136 : Nat := 4983230072969 + 3 ^ 40 * 782136 * 2
def baseEnd_782136 : Nat := 59498030397786240444893

theorem tailTrace_782136 : CollatzResearch.WordTrace tailWord_782136 prefixEnd_782136 59498030397786240444893 := by
  unfold tailWord_782136
  simp only [CollatzResearch.WordTrace]
  refine ⟨14263421747231162519603131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19017895662974883359470841 14263421747231162519603131)
  ·
    refine ⟨21395132620846743779404697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14263421747231162519603131 21395132620846743779404697)
    ·
      refine ⟨16046349465635057834553523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21395132620846743779404697 16046349465635057834553523)
      ·
        refine ⟨24069524198452586751830285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16046349465635057834553523 24069524198452586751830285)
        ·
          refine ⟨9026071574419720031936357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24069524198452586751830285 9026071574419720031936357)
          ·
            refine ⟨1692388420203697505988067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9026071574419720031936357 1692388420203697505988067)
            ·
              refine ⟨2538582630305546258982101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1692388420203697505988067 2538582630305546258982101)
              ·
                refine ⟨59498030397786240444893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2538582630305546258982101 59498030397786240444893)
                ·
                  rfl

theorem cell21_782136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 7].length) (baseStart_782136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_782136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_782136 prefixEnd_782136 := by exact prefixLift 782136
  have htrace : WordTrace (prefixWord ++ tailWord_782136) baseStart_782136 baseEnd_782136 := by
    simpa [prefixWord, tailWord_782136, baseEnd_782136] using wordTrace_append hprefix tailTrace_782136
  have hstable : (prefixWord ++ tailWord_782136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782136).length < 2 ^ (prefixWord ++ tailWord_782136).sum := by decide
  have hdescent : baseEnd_782136 < baseStart_782136 := by decide
  rcases family_descends (prefixWord ++ tailWord_782136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782142 : List Nat := [4, 2, 1, 2, 2, 3, 1, 3, 3]
def baseStart_782142 : Nat := 118140960795 + 782142 * 2 ^ 59
def prefixEnd_782142 : Nat := 4983230072969 + 3 ^ 40 * 782142 * 2
def baseEnd_782142 : Nat := 178495460475104044234667

theorem tailTrace_782142 : CollatzResearch.WordTrace tailWord_782142 prefixEnd_782142 178495460475104044234667 := by
  unfold tailWord_782142
  simp only [CollatzResearch.WordTrace]
  refine ⟨3565882791555073507990585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19018041554960392042616453 3565882791555073507990585)
  ·
    refine ⟨2674412093666305130992939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3565882791555073507990585 2674412093666305130992939)
    ·
      refine ⟨4011618140499457696489409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2674412093666305130992939 4011618140499457696489409)
      ·
        refine ⟨3008713605374593272367057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4011618140499457696489409 3008713605374593272367057)
        ·
          refine ⟨2256535204030944954275293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3008713605374593272367057 2256535204030944954275293)
          ·
            refine ⟨846200701511604357853235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2256535204030944954275293 846200701511604357853235)
            ·
              refine ⟨1269301052267406536779853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 846200701511604357853235 1269301052267406536779853)
              ·
                refine ⟨475987894600277451292445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1269301052267406536779853 475987894600277451292445)
                ·
                  refine ⟨178495460475104044234667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 475987894600277451292445 178495460475104044234667)
                  ·
                    rfl

theorem cell21_782142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_782142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_782142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_782142 prefixEnd_782142 := by exact prefixLift 782142
  have htrace : WordTrace (prefixWord ++ tailWord_782142) baseStart_782142 baseEnd_782142 := by
    simpa [prefixWord, tailWord_782142, baseEnd_782142] using wordTrace_append hprefix tailTrace_782142
  have hstable : (prefixWord ++ tailWord_782142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782142).length < 2 ^ (prefixWord ++ tailWord_782142).sum := by decide
  have hdescent : baseEnd_782142 < baseStart_782142 := by decide
  rcases family_descends (prefixWord ++ tailWord_782142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782215 : List Nat := [1, 1, 4, 2, 4, 1, 2, 2, 4]
def baseStart_782215 : Nat := 118140960795 + 782215 * 2 ^ 59
def prefixEnd_782215 : Nat := 4983230072969 + 3 ^ 40 * 782215 * 2
def baseEnd_782215 : Nat := 178512120069672139517851

theorem tailTrace_782215 : CollatzResearch.WordTrace tailWord_782215 prefixEnd_782215 178512120069672139517851 := by
  unfold tailWord_782215
  simp only [CollatzResearch.WordTrace]
  refine ⟨28529724861176121531332099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19019816574117414354221399 28529724861176121531332099)
  ·
    refine ⟨42794587291764182296998149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28529724861176121531332099 42794587291764182296998149)
    ·
      refine ⟨8023985117205784180687153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42794587291764182296998149 8023985117205784180687153)
      ·
        refine ⟨6017988837904338135515365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8023985117205784180687153 6017988837904338135515365)
        ·
          refine ⟨1128372907107063400409131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6017988837904338135515365 1128372907107063400409131)
          ·
            refine ⟨1692559360660595100613697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1128372907107063400409131 1692559360660595100613697)
            ·
              refine ⟨1269419520495446325460273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1692559360660595100613697 1269419520495446325460273)
              ·
                refine ⟨952064640371584744095205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1269419520495446325460273 952064640371584744095205)
                ·
                  refine ⟨178512120069672139517851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 952064640371584744095205 178512120069672139517851)
                  ·
                    rfl

theorem cell21_782215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 4].length) (baseStart_782215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_782215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_782215 prefixEnd_782215 := by exact prefixLift 782215
  have htrace : WordTrace (prefixWord ++ tailWord_782215) baseStart_782215 baseEnd_782215 := by
    simpa [prefixWord, tailWord_782215, baseEnd_782215] using wordTrace_append hprefix tailTrace_782215
  have hstable : (prefixWord ++ tailWord_782215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782215).length < 2 ^ (prefixWord ++ tailWord_782215).sum := by decide
  have hdescent : baseEnd_782215 < baseStart_782215 := by decide
  rcases family_descends (prefixWord ++ tailWord_782215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782271 : List Nat := [1, 1, 2, 2, 2, 1, 12]
def baseStart_782271 : Nat := 118140960795 + 782271 * 2 ^ 59
def prefixEnd_782271 : Nat := 4983230072969 + 3 ^ 40 * 782271 * 2
def baseEnd_782271 : Nat := 19836100003625387398267

theorem tailTrace_782271 : CollatzResearch.WordTrace tailWord_782271 prefixEnd_782271 19836100003625387398267 := by
  unfold tailWord_782271
  simp only [CollatzResearch.WordTrace]
  refine ⟨28531767348973243095370667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19021178232648828730247111 28531767348973243095370667)
  ·
    refine ⟨42797651023459864643056001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28531767348973243095370667 42797651023459864643056001)
    ·
      refine ⟨32098238267594898482292001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42797651023459864643056001 32098238267594898482292001)
      ·
        refine ⟨24073678700696173861719001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32098238267594898482292001 24073678700696173861719001)
        ·
          refine ⟨18055259025522130396289251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24073678700696173861719001 18055259025522130396289251)
          ·
            refine ⟨27082888538283195594433877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18055259025522130396289251 27082888538283195594433877)
            ·
              refine ⟨19836100003625387398267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 27082888538283195594433877 19836100003625387398267)
              ·
                rfl

theorem cell21_782271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 12].length) (baseStart_782271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_782271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_782271 prefixEnd_782271 := by exact prefixLift 782271
  have htrace : WordTrace (prefixWord ++ tailWord_782271) baseStart_782271 baseEnd_782271 := by
    simpa [prefixWord, tailWord_782271, baseEnd_782271] using wordTrace_append hprefix tailTrace_782271
  have hstable : (prefixWord ++ tailWord_782271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782271).length < 2 ^ (prefixWord ++ tailWord_782271).sum := by decide
  have hdescent : baseEnd_782271 < baseStart_782271 := by decide
  rcases family_descends (prefixWord ++ tailWord_782271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782333 : List Nat := [1, 4, 1, 1, 1, 2, 4, 1, 6]
def baseStart_782333 : Nat := 118140960795 + 782333 * 2 ^ 59
def prefixEnd_782333 : Nat := 4983230072969 + 3 ^ 40 * 782333 * 2
def baseEnd_782333 : Nat := 178539049277330156550943

theorem tailTrace_782333 : CollatzResearch.WordTrace tailWord_782333 prefixEnd_782333 178539049277330156550943 := by
  unfold tailWord_782333
  simp only [CollatzResearch.WordTrace]
  refine ⟨28534028674748627684127653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19022685783165751789418435 28534028674748627684127653)
  ·
    refine ⟨5350130376515367690773935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28534028674748627684127653 5350130376515367690773935)
    ·
      refine ⟨8025195564773051536160903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5350130376515367690773935 8025195564773051536160903)
      ·
        refine ⟨12037793347159577304241355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8025195564773051536160903 12037793347159577304241355)
        ·
          refine ⟨18056690020739365956362033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12037793347159577304241355 18056690020739365956362033)
          ·
            refine ⟨13542517515554524467271525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18056690020739365956362033 13542517515554524467271525)
            ·
              refine ⟨2539222034166473337613411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13542517515554524467271525 2539222034166473337613411)
              ·
                refine ⟨3808833051249710006420117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2539222034166473337613411 3808833051249710006420117)
                ·
                  refine ⟨178539049277330156550943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3808833051249710006420117 178539049277330156550943)
                  ·
                    rfl

theorem cell21_782333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_782333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_782333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_782333 prefixEnd_782333 := by exact prefixLift 782333
  have htrace : WordTrace (prefixWord ++ tailWord_782333) baseStart_782333 baseEnd_782333 := by
    simpa [prefixWord, tailWord_782333, baseEnd_782333] using wordTrace_append hprefix tailTrace_782333
  have hstable : (prefixWord ++ tailWord_782333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782333).length < 2 ^ (prefixWord ++ tailWord_782333).sum := by decide
  have hdescent : baseEnd_782333 < baseStart_782333 := by decide
  rcases family_descends (prefixWord ++ tailWord_782333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782342 : List Nat := [6, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_782342 : Nat := 118140960795 + 782342 * 2 ^ 59
def prefixEnd_782342 : Nat := 4983230072969 + 3 ^ 40 * 782342 * 2
def baseEnd_782342 : Nat := 178541103199948140900925

theorem tailTrace_782342 : CollatzResearch.WordTrace tailWord_782342 prefixEnd_782342 178541103199948140900925 := by
  unfold tailWord_782342
  simp only [CollatzResearch.WordTrace]
  refine ⟨891698654116125694412665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19022904621144014814136853 891698654116125694412665)
  ·
    refine ⟨668773990587094270809499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 891698654116125694412665 668773990587094270809499)
    ·
      refine ⟨1003160985880641406214249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 668773990587094270809499 1003160985880641406214249)
      ·
        refine ⟨752370739410481054660687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1003160985880641406214249 752370739410481054660687)
        ·
          refine ⟨1128556109115721581991031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 752370739410481054660687 1128556109115721581991031)
          ·
            refine ⟨1692834163673582372986547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1128556109115721581991031 1692834163673582372986547)
            ·
              refine ⟨2539251245510373559479821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1692834163673582372986547 2539251245510373559479821)
              ·
                refine ⟨952219217066390084804933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2539251245510373559479821 952219217066390084804933)
                ·
                  refine ⟨178541103199948140900925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 952219217066390084804933 178541103199948140900925)
                  ·
                    rfl

theorem cell21_782342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_782342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_782342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_782342 prefixEnd_782342 := by exact prefixLift 782342
  have htrace : WordTrace (prefixWord ++ tailWord_782342) baseStart_782342 baseEnd_782342 := by
    simpa [prefixWord, tailWord_782342, baseEnd_782342] using wordTrace_append hprefix tailTrace_782342
  have hstable : (prefixWord ++ tailWord_782342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782342).length < 2 ^ (prefixWord ++ tailWord_782342).sum := by decide
  have hdescent : baseEnd_782342 < baseStart_782342 := by decide
  rcases family_descends (prefixWord ++ tailWord_782342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782350 : List Nat := [4, 1, 1, 2, 2, 1, 3, 3, 4]
def baseStart_782350 : Nat := 118140960795 + 782350 * 2 ^ 59
def prefixEnd_782350 : Nat := 4983230072969 + 3 ^ 40 * 782350 * 2
def baseEnd_782350 : Nat := 178542928908941904767575

theorem tailTrace_782350 : CollatzResearch.WordTrace tailWord_782350 prefixEnd_782350 178542928908941904767575 := by
  unfold tailWord_782350
  simp only [CollatzResearch.WordTrace]
  refine ⟨3566831089460879948437063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19023099143791359724997669 3566831089460879948437063)
  ·
    refine ⟨5350246634191319922655595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3566831089460879948437063 5350246634191319922655595)
    ·
      refine ⟨8025369951286979883983393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5350246634191319922655595 8025369951286979883983393)
      ·
        refine ⟨6019027463465234912987545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8025369951286979883983393 6019027463465234912987545)
        ·
          refine ⟨4514270597598926184740659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6019027463465234912987545 4514270597598926184740659)
          ·
            refine ⟨6771405896398389277110989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4514270597598926184740659 6771405896398389277110989)
            ·
              refine ⟨2539277211149395978916621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6771405896398389277110989 2539277211149395978916621)
              ·
                refine ⟨952228954181023492093733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2539277211149395978916621 952228954181023492093733)
                ·
                  refine ⟨178542928908941904767575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 952228954181023492093733 178542928908941904767575)
                  ·
                    rfl

theorem cell21_782350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_782350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_782350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_782350 prefixEnd_782350 := by exact prefixLift 782350
  have htrace : WordTrace (prefixWord ++ tailWord_782350) baseStart_782350 baseEnd_782350 := by
    simpa [prefixWord, tailWord_782350, baseEnd_782350] using wordTrace_append hprefix tailTrace_782350
  have hstable : (prefixWord ++ tailWord_782350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782350).length < 2 ^ (prefixWord ++ tailWord_782350).sum := by decide
  have hdescent : baseEnd_782350 < baseStart_782350 := by decide
  rcases family_descends (prefixWord ++ tailWord_782350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782364 : List Nat := [2, 2, 3, 1, 3, 1, 2, 7]
def baseStart_782364 : Nat := 118140960795 + 782364 * 2 ^ 59
def prefixEnd_782364 : Nat := 4983230072969 + 3 ^ 40 * 782364 * 2
def baseEnd_782364 : Nat := 59515374633226997178071

theorem tailTrace_782364 : CollatzResearch.WordTrace tailWord_782364 prefixEnd_782364 59515374633226997178071 := by
  unfold tailWord_782364
  simp only [CollatzResearch.WordTrace]
  refine ⟨14267579668818159989253073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19023439558424213319004097 14267579668818159989253073)
  ·
    refine ⟨10700684751613619991939805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14267579668818159989253073 10700684751613619991939805)
    ·
      refine ⟨4012756781855107496977427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10700684751613619991939805 4012756781855107496977427)
      ·
        refine ⟨6019135172782661245466141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4012756781855107496977427 6019135172782661245466141)
        ·
          refine ⟨2257175689793497967049803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6019135172782661245466141 2257175689793497967049803)
          ·
            refine ⟨3385763534690246950574705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2257175689793497967049803 3385763534690246950574705)
            ·
              refine ⟨2539322651017685212931029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3385763534690246950574705 2539322651017685212931029)
              ·
                refine ⟨59515374633226997178071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2539322651017685212931029 59515374633226997178071)
                ·
                  rfl

theorem cell21_782364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 7].length) (baseStart_782364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_782364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_782364 prefixEnd_782364 := by exact prefixLift 782364
  have htrace : WordTrace (prefixWord ++ tailWord_782364) baseStart_782364 baseEnd_782364 := by
    simpa [prefixWord, tailWord_782364, baseEnd_782364] using wordTrace_append hprefix tailTrace_782364
  have hstable : (prefixWord ++ tailWord_782364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782364).length < 2 ^ (prefixWord ++ tailWord_782364).sum := by decide
  have hdescent : baseEnd_782364 < baseStart_782364 := by decide
  rcases family_descends (prefixWord ++ tailWord_782364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782395 : List Nat := [1, 1, 1, 1, 1, 2, 1, 10, 3]
def baseStart_782395 : Nat := 118140960795 + 782395 * 2 ^ 59
def prefixEnd_782395 : Nat := 4983230072969 + 3 ^ 40 * 782395 * 2
def baseEnd_782395 : Nat := 178553198522031826517483

theorem tailTrace_782395 : CollatzResearch.WordTrace tailWord_782395 prefixEnd_782395 178553198522031826517483 := by
  unfold tailWord_782395
  simp only [CollatzResearch.WordTrace]
  refine ⟨28536290000524012272884639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19024193333682674848589759 28536290000524012272884639)
  ·
    refine ⟨42804435000786018409326959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28536290000524012272884639 42804435000786018409326959)
    ·
      refine ⟨64206652501179027613990439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42804435000786018409326959 64206652501179027613990439)
      ·
        refine ⟨96309978751768541420985659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64206652501179027613990439 96309978751768541420985659)
        ·
          refine ⟨144464968127652812131478489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96309978751768541420985659 144464968127652812131478489)
          ·
            refine ⟨108348726095739609098608867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144464968127652812131478489 108348726095739609098608867)
            ·
              refine ⟨162523089143609413647913301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108348726095739609098608867 162523089143609413647913301)
              ·
                refine ⟨476141862725418204046621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 162523089143609413647913301 476141862725418204046621)
                ·
                  refine ⟨178553198522031826517483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 476141862725418204046621 178553198522031826517483)
                  ·
                    rfl

theorem cell21_782395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 10, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 10, 3].length) (baseStart_782395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_782395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_782395 prefixEnd_782395 := by exact prefixLift 782395
  have htrace : WordTrace (prefixWord ++ tailWord_782395) baseStart_782395 baseEnd_782395 := by
    simpa [prefixWord, tailWord_782395, baseEnd_782395] using wordTrace_append hprefix tailTrace_782395
  have hstable : (prefixWord ++ tailWord_782395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782395).length < 2 ^ (prefixWord ++ tailWord_782395).sum := by decide
  have hdescent : baseEnd_782395 < baseStart_782395 := by decide
  rcases family_descends (prefixWord ++ tailWord_782395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782398 : List Nat := [4, 2, 1, 3, 2, 2, 1, 6]
def baseStart_782398 : Nat := 118140960795 + 782398 * 2 ^ 59
def prefixEnd_782398 : Nat := 4983230072969 + 3 ^ 40 * 782398 * 2
def baseEnd_782398 : Nat := 59517961054301495989159

theorem tailTrace_782398 : CollatzResearch.WordTrace tailWord_782398 prefixEnd_782398 59517961054301495989159 := by
  unfold tailWord_782398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3567049927439142973155481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19024266279675429190162565 3567049927439142973155481)
  ·
    refine ⟨2675287445579357229866611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3567049927439142973155481 2675287445579357229866611)
    ·
      refine ⟨4012931168369035844799917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2675287445579357229866611 4012931168369035844799917)
      ·
        refine ⟨1504849188138388441799969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4012931168369035844799917 1504849188138388441799969)
        ·
          refine ⟨1128636891103791331349977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1504849188138388441799969 1128636891103791331349977)
          ·
            refine ⟨846477668327843498512483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1128636891103791331349977 846477668327843498512483)
            ·
              refine ⟨1269716502491765247768725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 846477668327843498512483 1269716502491765247768725)
              ·
                refine ⟨59517961054301495989159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1269716502491765247768725 59517961054301495989159)
                ·
                  rfl

theorem cell21_782398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_782398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_782398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_782398 prefixEnd_782398 := by exact prefixLift 782398
  have htrace : WordTrace (prefixWord ++ tailWord_782398) baseStart_782398 baseEnd_782398 := by
    simpa [prefixWord, tailWord_782398, baseEnd_782398] using wordTrace_append hprefix tailTrace_782398
  have hstable : (prefixWord ++ tailWord_782398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782398).length < 2 ^ (prefixWord ++ tailWord_782398).sum := by decide
  have hdescent : baseEnd_782398 < baseStart_782398 := by decide
  rcases family_descends (prefixWord ++ tailWord_782398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782409 : List Nat := [1, 2, 1, 1, 2, 2, 3, 5, 4]
def baseStart_782409 : Nat := 118140960795 + 782409 * 2 ^ 59
def prefixEnd_782409 : Nat := 4983230072969 + 3 ^ 40 * 782409 * 2
def baseEnd_782409 : Nat := 178556393512770913284121

theorem tailTrace_782409 : CollatzResearch.WordTrace tailWord_782409 prefixEnd_782409 178556393512770913284121 := by
  unfold tailWord_782409
  simp only [CollatzResearch.WordTrace]
  refine ⟨28536800622473292663894281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19024533748315528442596187 28536800622473292663894281)
  ·
    refine ⟨21402600466854969497920711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28536800622473292663894281 21402600466854969497920711)
    ·
      refine ⟨32103900700282454246881067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21402600466854969497920711 32103900700282454246881067)
      ·
        refine ⟨48155851050423681370321601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32103900700282454246881067 48155851050423681370321601)
        ·
          refine ⟨36116888287817761027741201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48155851050423681370321601 36116888287817761027741201)
          ·
            refine ⟨27087666215863320770805901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36116888287817761027741201 27087666215863320770805901)
            ·
              refine ⟨10157874830948745289052213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27087666215863320770805901 10157874830948745289052213)
              ·
                refine ⟨952300765401444870848645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10157874830948745289052213 952300765401444870848645)
                ·
                  refine ⟨178556393512770913284121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 952300765401444870848645 178556393512770913284121)
                  ·
                    rfl

theorem cell21_782409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 4].length) (baseStart_782409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_782409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_782409 prefixEnd_782409 := by exact prefixLift 782409
  have htrace : WordTrace (prefixWord ++ tailWord_782409) baseStart_782409 baseEnd_782409 := by
    simpa [prefixWord, tailWord_782409, baseEnd_782409] using wordTrace_append hprefix tailTrace_782409
  have hstable : (prefixWord ++ tailWord_782409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782409).length < 2 ^ (prefixWord ++ tailWord_782409).sum := by decide
  have hdescent : baseEnd_782409 < baseStart_782409 := by decide
  rcases family_descends (prefixWord ++ tailWord_782409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782423 : List Nat := [1, 1, 3, 2, 2, 1, 2, 9]
def baseStart_782423 : Nat := 118140960795 + 782423 * 2 ^ 59
def prefixEnd_782423 : Nat := 4983230072969 + 3 ^ 40 * 782423 * 2
def baseEnd_782423 : Nat := 59519862834503333350253

theorem tailTrace_782423 : CollatzResearch.WordTrace tailWord_782423 prefixEnd_782423 59519862834503333350253 := by
  unfold tailWord_782423
  simp only [CollatzResearch.WordTrace]
  refine ⟨28537311244422573054903923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19024874162948382036602615 28537311244422573054903923)
  ·
    refine ⟨42805966866633859582355885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28537311244422573054903923 42805966866633859582355885)
    ·
      refine ⟨16052237574987697343383457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42805966866633859582355885 16052237574987697343383457)
      ·
        refine ⟨12039178181240773007537593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16052237574987697343383457 12039178181240773007537593)
        ·
          refine ⟨9029383635930579755653195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12039178181240773007537593 9029383635930579755653195)
          ·
            refine ⟨13544075453895869633479793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9029383635930579755653195 13544075453895869633479793)
            ·
              refine ⟨10158056590421902225109845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13544075453895869633479793 10158056590421902225109845)
              ·
                refine ⟨59519862834503333350253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10158056590421902225109845 59519862834503333350253)
                ·
                  rfl

theorem cell21_782423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 9].length) (baseStart_782423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_782423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_782423 prefixEnd_782423 := by exact prefixLift 782423
  have htrace : WordTrace (prefixWord ++ tailWord_782423) baseStart_782423 baseEnd_782423 := by
    simpa [prefixWord, tailWord_782423, baseEnd_782423] using wordTrace_append hprefix tailTrace_782423
  have hstable : (prefixWord ++ tailWord_782423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782423).length < 2 ^ (prefixWord ++ tailWord_782423).sum := by decide
  have hdescent : baseEnd_782423 < baseStart_782423 := by decide
  rcases family_descends (prefixWord ++ tailWord_782423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782429 : List Nat := [1, 4, 4, 1, 1, 1, 1, 5, 3]
def baseStart_782429 : Nat := 118140960795 + 782429 * 2 ^ 59
def prefixEnd_782429 : Nat := 4983230072969 + 3 ^ 40 * 782429 * 2
def baseEnd_782429 : Nat := 178560957785255322950747

theorem tailTrace_782429 : CollatzResearch.WordTrace tailWord_782429 prefixEnd_782429 178560957785255322950747 := by
  unfold tailWord_782429
  simp only [CollatzResearch.WordTrace]
  refine ⟨28537530082400836079622341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19025020054933890719748227 28537530082400836079622341)
  ·
    refine ⟨5350786890450156764929189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28537530082400836079622341 5350786890450156764929189)
    ·
      refine ⟨1003272541959404393424223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5350786890450156764929189 1003272541959404393424223)
      ·
        refine ⟨1504908812939106590136335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1003272541959404393424223 1504908812939106590136335)
        ·
          refine ⟨2257363219408659885204503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1504908812939106590136335 2257363219408659885204503)
          ·
            refine ⟨3386044829112989827806755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2257363219408659885204503 3386044829112989827806755)
            ·
              refine ⟨5079067243669484741710133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3386044829112989827806755 5079067243669484741710133)
              ·
                refine ⟨476162554094014194535325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5079067243669484741710133 476162554094014194535325)
                ·
                  refine ⟨178560957785255322950747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 476162554094014194535325 178560957785255322950747)
                  ·
                    rfl

theorem cell21_782429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_782429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_782429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_782429 prefixEnd_782429 := by exact prefixLift 782429
  have htrace : WordTrace (prefixWord ++ tailWord_782429) baseStart_782429 baseEnd_782429 := by
    simpa [prefixWord, tailWord_782429, baseEnd_782429] using wordTrace_append hprefix tailTrace_782429
  have hstable : (prefixWord ++ tailWord_782429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782429).length < 2 ^ (prefixWord ++ tailWord_782429).sum := by decide
  have hdescent : baseEnd_782429 < baseStart_782429 := by decide
  rcases family_descends (prefixWord ++ tailWord_782429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782519 : List Nat := [1, 1, 3, 1, 4, 4, 2, 1, 4]
def baseStart_782519 : Nat := 118140960795 + 782519 * 2 ^ 59
def prefixEnd_782519 : Nat := 4983230072969 + 3 ^ 40 * 782519 * 2
def baseEnd_782519 : Nat := 178581497011435166450563

theorem tailTrace_782519 : CollatzResearch.WordTrace tailWord_782519 prefixEnd_782519 178581497011435166450563 := by
  unfold tailWord_782519
  simp only [CollatzResearch.WordTrace]
  refine ⟨28540812652074781450398611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19027208434716520966932407 28540812652074781450398611)
  ·
    refine ⟨42811218978112172175597917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28540812652074781450398611 42811218978112172175597917)
    ·
      refine ⟨16054207116792064565849219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42811218978112172175597917 16054207116792064565849219)
      ·
        refine ⟨24081310675188096848773829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16054207116792064565849219 24081310675188096848773829)
        ·
          refine ⟨4515245751597768159145093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24081310675188096848773829 4515245751597768159145093)
          ·
            refine ⟨846608578424581529839705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4515245751597768159145093 846608578424581529839705)
            ·
              refine ⟨634956433818436147379779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 846608578424581529839705 634956433818436147379779)
              ·
                refine ⟨952434650727654221069669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 634956433818436147379779 952434650727654221069669)
                ·
                  refine ⟨178581497011435166450563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 952434650727654221069669 178581497011435166450563)
                  ·
                    rfl

theorem cell21_782519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 4].length) (baseStart_782519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_782519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_782519 prefixEnd_782519 := by exact prefixLift 782519
  have htrace : WordTrace (prefixWord ++ tailWord_782519) baseStart_782519 baseEnd_782519 := by
    simpa [prefixWord, tailWord_782519, baseEnd_782519] using wordTrace_append hprefix tailTrace_782519
  have hstable : (prefixWord ++ tailWord_782519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782519).length < 2 ^ (prefixWord ++ tailWord_782519).sum := by decide
  have hdescent : baseEnd_782519 < baseStart_782519 := by decide
  rcases family_descends (prefixWord ++ tailWord_782519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782556 : List Nat := [2, 2, 5, 2, 2, 1, 2, 2, 3]
def baseStart_782556 : Nat := 118140960795 + 782556 * 2 ^ 59
def prefixEnd_782556 : Nat := 4983230072969 + 3 ^ 40 * 782556 * 2
def baseEnd_782556 : Nat := 178589940915531324333821

theorem tailTrace_782556 : CollatzResearch.WordTrace tailWord_782556 prefixEnd_782556 178589940915531324333821 := by
  unfold tailWord_782556
  simp only [CollatzResearch.WordTrace]
  refine ⟨14271081076470368384747761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19028108101960491179663681 14271081076470368384747761)
  ·
    refine ⟨10703310807352776288560821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14271081076470368384747761 10703310807352776288560821)
    ·
      refine ⟨1003435388189322777052577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10703310807352776288560821 1003435388189322777052577)
      ·
        refine ⟨752576541141992082789433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1003435388189322777052577 752576541141992082789433)
        ·
          refine ⟨564432405856494062092075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 752576541141992082789433 564432405856494062092075)
          ·
            refine ⟨846648608784741093138113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564432405856494062092075 846648608784741093138113)
            ·
              refine ⟨634986456588555819853585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 846648608784741093138113 634986456588555819853585)
              ·
                refine ⟨476239842441416864890189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 634986456588555819853585 476239842441416864890189)
                ·
                  refine ⟨178589940915531324333821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 476239842441416864890189 178589940915531324333821)
                  ·
                    rfl

theorem cell21_782556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 2, 3].length) (baseStart_782556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_782556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_782556 prefixEnd_782556 := by exact prefixLift 782556
  have htrace : WordTrace (prefixWord ++ tailWord_782556) baseStart_782556 baseEnd_782556 := by
    simpa [prefixWord, tailWord_782556, baseEnd_782556] using wordTrace_append hprefix tailTrace_782556
  have hstable : (prefixWord ++ tailWord_782556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782556).length < 2 ^ (prefixWord ++ tailWord_782556).sum := by decide
  have hdescent : baseEnd_782556 < baseStart_782556 := by decide
  rcases family_descends (prefixWord ++ tailWord_782556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782578 : List Nat := [3, 2, 1, 3, 2, 1, 2, 3, 4]
def baseStart_782578 : Nat := 118140960795 + 782578 * 2 ^ 59
def prefixEnd_782578 : Nat := 4983230072969 + 3 ^ 40 * 782578 * 2
def baseEnd_782578 : Nat := 178594961615264174967109

theorem tailTrace_782578 : CollatzResearch.WordTrace tailWord_782578 prefixEnd_782578 178594961615264174967109 := by
  unfold tailWord_782578
  simp only [CollatzResearch.WordTrace]
  refine ⟨7135741139715258631699097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19028643039240689684530925 7135741139715258631699097)
  ·
    refine ⟨5351805854786443973774323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7135741139715258631699097 5351805854786443973774323)
    ·
      refine ⟨8027708782179665960661485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5351805854786443973774323 8027708782179665960661485)
      ·
        refine ⟨3010390793317374735248057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8027708782179665960661485 3010390793317374735248057)
        ·
          refine ⟨2257793094988031051436043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3010390793317374735248057 2257793094988031051436043)
          ·
            refine ⟨3386689642482046577154065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2257793094988031051436043 3386689642482046577154065)
            ·
              refine ⟨2540017231861534932865549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3386689642482046577154065 2540017231861534932865549)
              ·
                refine ⟨952506461948075599824581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2540017231861534932865549 952506461948075599824581)
                ·
                  refine ⟨178594961615264174967109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 952506461948075599824581 178594961615264174967109)
                  ·
                    rfl

theorem cell21_782578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_782578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_782578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_782578 prefixEnd_782578 := by exact prefixLift 782578
  have htrace : WordTrace (prefixWord ++ tailWord_782578) baseStart_782578 baseEnd_782578 := by
    simpa [prefixWord, tailWord_782578, baseEnd_782578] using wordTrace_append hprefix tailTrace_782578
  have hstable : (prefixWord ++ tailWord_782578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782578).length < 2 ^ (prefixWord ++ tailWord_782578).sum := by decide
  have hdescent : baseEnd_782578 < baseStart_782578 := by decide
  rcases family_descends (prefixWord ++ tailWord_782578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782606 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 7]
def baseStart_782606 : Nat := 118140960795 + 782606 * 2 ^ 59
def prefixEnd_782606 : Nat := 4983230072969 + 3 ^ 40 * 782606 * 2
def baseEnd_782606 : Nat := 178601351596742348500385

theorem tailTrace_782606 : CollatzResearch.WordTrace tailWord_782606 prefixEnd_782606 178601351596742348500385 := by
  unfold tailWord_782606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3567998225344949413601959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19029323868506396872543781 3567998225344949413601959)
  ·
    refine ⟨5351997338017424120402939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3567998225344949413601959 5351997338017424120402939)
    ·
      refine ⟨8027996007026136180604409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5351997338017424120402939 8027996007026136180604409)
      ·
        refine ⟨6020997005269602135453307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8027996007026136180604409 6020997005269602135453307)
        ·
          refine ⟨9031495507904403203179961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6020997005269602135453307 9031495507904403203179961)
          ·
            refine ⟨6773621630928302402384971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9031495507904403203179961 6773621630928302402384971)
            ·
              refine ⟨10160432446392453603577457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6773621630928302402384971 10160432446392453603577457)
              ·
                refine ⟨7620324334794340202683093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10160432446392453603577457 7620324334794340202683093)
                ·
                  refine ⟨178601351596742348500385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7620324334794340202683093 178601351596742348500385)
                  ·
                    rfl

theorem cell21_782606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_782606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_782606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_782606 prefixEnd_782606 := by exact prefixLift 782606
  have htrace : WordTrace (prefixWord ++ tailWord_782606) baseStart_782606 baseEnd_782606 := by
    simpa [prefixWord, tailWord_782606, baseEnd_782606] using wordTrace_append hprefix tailTrace_782606
  have hstable : (prefixWord ++ tailWord_782606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782606).length < 2 ^ (prefixWord ++ tailWord_782606).sum := by decide
  have hdescent : baseEnd_782606 < baseStart_782606 := by decide
  rcases family_descends (prefixWord ++ tailWord_782606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782623 : List Nat := [1, 1, 2, 4, 3, 2, 2, 1, 5]
def baseStart_782623 : Nat := 118140960795 + 782623 * 2 ^ 59
def prefixEnd_782623 : Nat := 4983230072969 + 3 ^ 40 * 782623 * 2
def baseEnd_782623 : Nat := 178605231228354096717017

theorem tailTrace_782623 : CollatzResearch.WordTrace tailWord_782623 prefixEnd_782623 178605231228354096717017 := by
  unfold tailWord_782623
  simp only [CollatzResearch.WordTrace]
  refine ⟨28544605843698007212184523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19029737229132004808123015 28544605843698007212184523)
  ·
    refine ⟨42816908765547010818276785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28544605843698007212184523 42816908765547010818276785)
    ·
      refine ⟨32112681574160258113707589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42816908765547010818276785 32112681574160258113707589)
      ·
        refine ⟨6021127795155048396320173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32112681574160258113707589 6021127795155048396320173)
        ·
          refine ⟨2257922923183143148620065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6021127795155048396320173 2257922923183143148620065)
          ·
            refine ⟨1693442192387357361465049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2257922923183143148620065 1693442192387357361465049)
            ·
              refine ⟨1270081644290518021098787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1693442192387357361465049 1270081644290518021098787)
              ·
                refine ⟨1905122466435777031648181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1270081644290518021098787 1905122466435777031648181)
                ·
                  refine ⟨178605231228354096717017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1905122466435777031648181 178605231228354096717017)
                  ·
                    rfl

theorem cell21_782623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 5].length) (baseStart_782623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_782623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_782623 prefixEnd_782623 := by exact prefixLift 782623
  have htrace : WordTrace (prefixWord ++ tailWord_782623) baseStart_782623 baseEnd_782623 := by
    simpa [prefixWord, tailWord_782623, baseEnd_782623] using wordTrace_append hprefix tailTrace_782623
  have hstable : (prefixWord ++ tailWord_782623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782623).length < 2 ^ (prefixWord ++ tailWord_782623).sum := by decide
  have hdescent : baseEnd_782623 < baseStart_782623 := by decide
  rcases family_descends (prefixWord ++ tailWord_782623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782688 : List Nat := [2, 1, 1, 3, 6, 1, 2, 1, 4]
def baseStart_782688 : Nat := 118140960795 + 782688 * 2 ^ 59
def prefixEnd_782688 : Nat := 4983230072969 + 3 ^ 40 * 782688 * 2
def baseEnd_782688 : Nat := 178620065113928428133551

theorem tailTrace_782688 : CollatzResearch.WordTrace tailWord_782688 prefixEnd_782688 178620065113928428133551 := by
  unfold tailWord_782688
  simp only [CollatzResearch.WordTrace]
  refine ⟨14273488294231261656650359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19031317725641682208867145 14273488294231261656650359)
  ·
    refine ⟨21410232441346892484975539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14273488294231261656650359 21410232441346892484975539)
    ·
      refine ⟨32115348662020338727463309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21410232441346892484975539 32115348662020338727463309)
      ·
        refine ⟨12043255748257627022798741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32115348662020338727463309 12043255748257627022798741)
        ·
          refine ⟨564527613199576266693691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12043255748257627022798741 564527613199576266693691)
          ·
            refine ⟨846791419799364400040537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564527613199576266693691 846791419799364400040537)
            ·
              refine ⟨635093564849523300030403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 846791419799364400040537 635093564849523300030403)
              ·
                refine ⟨952640347274284950045605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635093564849523300030403 952640347274284950045605)
                ·
                  refine ⟨178620065113928428133551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 952640347274284950045605 178620065113928428133551)
                  ·
                    rfl

theorem cell21_782688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 4].length) (baseStart_782688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_782688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_782688 prefixEnd_782688 := by exact prefixLift 782688
  have htrace : WordTrace (prefixWord ++ tailWord_782688) baseStart_782688 baseEnd_782688 := by
    simpa [prefixWord, tailWord_782688, baseEnd_782688] using wordTrace_append hprefix tailTrace_782688
  have hstable : (prefixWord ++ tailWord_782688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782688).length < 2 ^ (prefixWord ++ tailWord_782688).sum := by decide
  have hdescent : baseEnd_782688 < baseStart_782688 := by decide
  rcases family_descends (prefixWord ++ tailWord_782688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782744 : List Nat := [2, 1, 2, 5, 1, 1, 3, 6]
def baseStart_782744 : Nat := 118140960795 + 782744 * 2 ^ 59
def prefixEnd_782744 : Nat := 4983230072969 + 3 ^ 40 * 782744 * 2
def baseEnd_782744 : Nat := 59544281692294925066701

theorem tailTrace_782744 : CollatzResearch.WordTrace tailWord_782744 prefixEnd_782744 59544281692294925066701 := by
  unfold tailWord_782744
  simp only [CollatzResearch.WordTrace]
  refine ⟨14274509538129822438669643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19032679384173096584892857 14274509538129822438669643)
  ·
    refine ⟨21411764307194733658004465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14274509538129822438669643 21411764307194733658004465)
    ·
      refine ⟨16058823230396050243503349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21411764307194733658004465 16058823230396050243503349)
      ·
        refine ⟨1505514677849629710328439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16058823230396050243503349 1505514677849629710328439)
        ·
          refine ⟨2258272016774444565492659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1505514677849629710328439 2258272016774444565492659)
          ·
            refine ⟨3387408025161666848238989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2258272016774444565492659 3387408025161666848238989)
            ·
              refine ⟨1270278009435625068089621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3387408025161666848238989 1270278009435625068089621)
              ·
                refine ⟨59544281692294925066701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1270278009435625068089621 59544281692294925066701)
                ·
                  rfl

theorem cell21_782744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 6].length) (baseStart_782744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_782744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_782744 prefixEnd_782744 := by exact prefixLift 782744
  have htrace : WordTrace (prefixWord ++ tailWord_782744) baseStart_782744 baseEnd_782744 := by
    simpa [prefixWord, tailWord_782744, baseEnd_782744] using wordTrace_append hprefix tailTrace_782744
  have hstable : (prefixWord ++ tailWord_782744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782744).length < 2 ^ (prefixWord ++ tailWord_782744).sum := by decide
  have hdescent : baseEnd_782744 < baseStart_782744 := by decide
  rcases family_descends (prefixWord ++ tailWord_782744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782775 : List Nat := [1, 1, 3, 1, 3, 3, 1, 5, 3]
def baseStart_782775 : Nat := 118140960795 + 782775 * 2 ^ 59
def prefixEnd_782775 : Nat := 4983230072969 + 3 ^ 40 * 782775 * 2
def baseEnd_782775 : Nat := 178639919699235610183373

theorem tailTrace_782775 : CollatzResearch.WordTrace tailWord_782775 prefixEnd_782775 178639919699235610183373 := by
  unfold tailWord_782775
  simp only [CollatzResearch.WordTrace]
  refine ⟨28550149739147337171717779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19033433159431558114478519 28550149739147337171717779)
  ·
    refine ⟨42825224608721005757576669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28550149739147337171717779 42825224608721005757576669)
    ·
      refine ⟨16059459228270377159091251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42825224608721005757576669 16059459228270377159091251)
      ·
        refine ⟨24089188842405565738636877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16059459228270377159091251 24089188842405565738636877)
        ·
          refine ⟨9033445815902087151988829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24089188842405565738636877 9033445815902087151988829)
          ·
            refine ⟨3387542180963282681995811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9033445815902087151988829 3387542180963282681995811)
            ·
              refine ⟨5081313271444924022993717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3387542180963282681995811 5081313271444924022993717)
              ·
                refine ⟨476373119197961627155661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5081313271444924022993717 476373119197961627155661)
                ·
                  refine ⟨178639919699235610183373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 476373119197961627155661 178639919699235610183373)
                  ·
                    rfl

theorem cell21_782775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 5, 3].length) (baseStart_782775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_782775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_782775 prefixEnd_782775 := by exact prefixLift 782775
  have htrace : WordTrace (prefixWord ++ tailWord_782775) baseStart_782775 baseEnd_782775 := by
    simpa [prefixWord, tailWord_782775, baseEnd_782775] using wordTrace_append hprefix tailTrace_782775
  have hstable : (prefixWord ++ tailWord_782775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782775).length < 2 ^ (prefixWord ++ tailWord_782775).sum := by decide
  have hdescent : baseEnd_782775 < baseStart_782775 := by decide
  rcases family_descends (prefixWord ++ tailWord_782775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782837 : List Nat := [1, 3, 5, 1, 2, 2, 7]
def baseStart_782837 : Nat := 118140960795 + 782837 * 2 ^ 59
def prefixEnd_782837 : Nat := 4983230072969 + 3 ^ 40 * 782837 * 2
def baseEnd_782837 : Nat := 19850452104881920016657

theorem tailTrace_782837 : CollatzResearch.WordTrace tailWord_782837 prefixEnd_782837 19850452104881920016657 := by
  unfold tailWord_782837
  simp only [CollatzResearch.WordTrace]
  refine ⟨28552411064922721760474765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19034940709948481173649843 28552411064922721760474765)
  ·
    refine ⟨10707154149346020660178037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28552411064922721760474765 10707154149346020660178037)
    ·
      refine ⟨1003795701501189436891691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10707154149346020660178037 1003795701501189436891691)
      ·
        refine ⟨1505693552251784155337537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1003795701501189436891691 1505693552251784155337537)
        ·
          refine ⟨1129270164188838116503153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1505693552251784155337537 1129270164188838116503153)
          ·
            refine ⟨846952623141628587377365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1129270164188838116503153 846952623141628587377365)
            ·
              refine ⟨19850452104881920016657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 846952623141628587377365 19850452104881920016657)
              ·
                rfl

theorem cell21_782837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 7].length) (baseStart_782837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_782837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_782837 prefixEnd_782837 := by exact prefixLift 782837
  have htrace : WordTrace (prefixWord ++ tailWord_782837) baseStart_782837 baseEnd_782837 := by
    simpa [prefixWord, tailWord_782837, baseEnd_782837] using wordTrace_append hprefix tailTrace_782837
  have hstable : (prefixWord ++ tailWord_782837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782837).length < 2 ^ (prefixWord ++ tailWord_782837).sum := by decide
  have hdescent : baseEnd_782837 < baseStart_782837 := by decide
  rcases family_descends (prefixWord ++ tailWord_782837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782854 : List Nat := [6, 2, 1, 1, 1, 1, 1, 8]
def baseStart_782854 : Nat := 118140960795 + 782854 * 2 ^ 59
def prefixEnd_782854 : Nat := 4983230072969 + 3 ^ 40 * 782854 * 2
def baseEnd_782854 : Nat := 59552649525183009455515

theorem tailTrace_782854 : CollatzResearch.WordTrace tailWord_782854 prefixEnd_782854 59552649525183009455515 := by
  unfold tailWord_782854
  simp only [CollatzResearch.WordTrace]
  refine ⟨892282222058160426995113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19035354070574089109229077 892282222058160426995113)
  ·
    refine ⟨669211666543620320246335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 892282222058160426995113 669211666543620320246335)
    ·
      refine ⟨1003817499815430480369503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 669211666543620320246335 1003817499815430480369503)
      ·
        refine ⟨1505726249723145720554255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1003817499815430480369503 1505726249723145720554255)
        ·
          refine ⟨2258589374584718580831383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1505726249723145720554255 2258589374584718580831383)
          ·
            refine ⟨3387884061877077871247075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2258589374584718580831383 3387884061877077871247075)
            ·
              refine ⟨5081826092815616806870613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3387884061877077871247075 5081826092815616806870613)
              ·
                refine ⟨59552649525183009455515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5081826092815616806870613 59552649525183009455515)
                ·
                  rfl

theorem cell21_782854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_782854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_782854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_782854 prefixEnd_782854 := by exact prefixLift 782854
  have htrace : WordTrace (prefixWord ++ tailWord_782854) baseStart_782854 baseEnd_782854 := by
    simpa [prefixWord, tailWord_782854, baseEnd_782854] using wordTrace_append hprefix tailTrace_782854
  have hstable : (prefixWord ++ tailWord_782854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782854).length < 2 ^ (prefixWord ++ tailWord_782854).sum := by decide
  have hdescent : baseEnd_782854 < baseStart_782854 := by decide
  rcases family_descends (prefixWord ++ tailWord_782854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782902 : List Nat := [5, 1, 2, 1, 2, 3, 2, 2, 3]
def baseStart_782902 : Nat := 118140960795 + 782902 * 2 ^ 59
def prefixEnd_782902 : Nat := 4983230072969 + 3 ^ 40 * 782902 * 2
def baseEnd_782902 : Nat := 178668902829511611566447

theorem tailTrace_782902 : CollatzResearch.WordTrace tailWord_782902 prefixEnd_782902 178668902829511611566447 := by
  unfold tailWord_782902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1784673863105452366349435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19036521206458158574393973 1784673863105452366349435)
  ·
    refine ⟨2677010794658178549524153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1784673863105452366349435 2677010794658178549524153)
    ·
      refine ⟨2007758095993633912143115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2677010794658178549524153 2007758095993633912143115)
      ·
        refine ⟨3011637143990450868214673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2007758095993633912143115 3011637143990450868214673)
        ·
          refine ⟨2258727857992838151161005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3011637143990450868214673 2258727857992838151161005)
          ·
            refine ⟨847022946747314306685377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2258727857992838151161005 847022946747314306685377)
            ·
              refine ⟨635267210060485730014033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 847022946747314306685377 635267210060485730014033)
              ·
                refine ⟨476450407545364297510525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 635267210060485730014033 476450407545364297510525)
                ·
                  refine ⟨178668902829511611566447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 476450407545364297510525 178668902829511611566447)
                  ·
                    rfl

theorem cell21_782902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_782902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_782902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_782902 prefixEnd_782902 := by exact prefixLift 782902
  have htrace : WordTrace (prefixWord ++ tailWord_782902) baseStart_782902 baseEnd_782902 := by
    simpa [prefixWord, tailWord_782902, baseEnd_782902] using wordTrace_append hprefix tailTrace_782902
  have hstable : (prefixWord ++ tailWord_782902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782902).length < 2 ^ (prefixWord ++ tailWord_782902).sum := by decide
  have hdescent : baseEnd_782902 < baseStart_782902 := by decide
  rcases family_descends (prefixWord ++ tailWord_782902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782958 : List Nat := [4, 1, 2, 2, 2, 1, 3, 2, 4]
def baseStart_782958 : Nat := 118140960795 + 782958 * 2 ^ 59
def prefixEnd_782958 : Nat := 4983230072969 + 3 ^ 40 * 782958 * 2
def baseEnd_782958 : Nat := 178681682792467958632999

theorem tailTrace_782958 : CollatzResearch.WordTrace tailWord_782958 prefixEnd_782958 178681682792467958632999 := by
  unfold tailWord_782958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3569603037185544928203691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19037882864989572950419685 3569603037185544928203691)
  ·
    refine ⟨5354404555778317392305537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3569603037185544928203691 5354404555778317392305537)
    ·
      refine ⟨4015803416833738044229153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5354404555778317392305537 4015803416833738044229153)
      ·
        refine ⟨3011852562625303533171865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4015803416833738044229153 3011852562625303533171865)
        ·
          refine ⟨2258889421968977649878899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3011852562625303533171865 2258889421968977649878899)
          ·
            refine ⟨3388334132953466474818349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2258889421968977649878899 3388334132953466474818349)
            ·
              refine ⟨1270625299857549928056881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3388334132953466474818349 1270625299857549928056881)
              ·
                refine ⟨952968974893162446042661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1270625299857549928056881 952968974893162446042661)
                ·
                  refine ⟨178681682792467958632999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 952968974893162446042661 178681682792467958632999)
                  ·
                    rfl

theorem cell21_782958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_782958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_782958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_782958 prefixEnd_782958 := by exact prefixLift 782958
  have htrace : WordTrace (prefixWord ++ tailWord_782958) baseStart_782958 baseEnd_782958 := by
    simpa [prefixWord, tailWord_782958, baseEnd_782958] using wordTrace_append hprefix tailTrace_782958
  have hstable : (prefixWord ++ tailWord_782958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782958).length < 2 ^ (prefixWord ++ tailWord_782958).sum := by decide
  have hdescent : baseEnd_782958 < baseStart_782958 := by decide
  rcases family_descends (prefixWord ++ tailWord_782958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783000 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 8]
def baseStart_783000 : Nat := 118140960795 + 783000 * 2 ^ 59
def prefixEnd_783000 : Nat := 4983230072969 + 3 ^ 40 * 783000 * 2
def baseEnd_783000 : Nat := 178691267764685218932913

theorem tailTrace_783000 : CollatzResearch.WordTrace tailWord_783000 prefixEnd_783000 178691267764685218932913 := by
  unfold tailWord_783000
  simp only [CollatzResearch.WordTrace]
  refine ⟨14279178081666100299329227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19038904108888133732438969 14279178081666100299329227)
  ·
    refine ⟨21418767122499150448993841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14279178081666100299329227 21418767122499150448993841)
    ·
      refine ⟨16064075341874362836745381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21418767122499150448993841 16064075341874362836745381)
      ·
        refine ⟨3012014126601443031889759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16064075341874362836745381 3012014126601443031889759)
        ·
          refine ⟨4518021189902164547834639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3012014126601443031889759 4518021189902164547834639)
          ·
            refine ⟨6777031784853246821751959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4518021189902164547834639 6777031784853246821751959)
            ·
              refine ⟨10165547677279870232627939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6777031784853246821751959 10165547677279870232627939)
              ·
                refine ⟨15248321515919805348941909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10165547677279870232627939 15248321515919805348941909)
                ·
                  refine ⟨178691267764685218932913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15248321515919805348941909 178691267764685218932913)
                  ·
                    rfl

theorem cell21_783000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 8].length) (baseStart_783000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_783000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_783000 prefixEnd_783000 := by exact prefixLift 783000
  have htrace : WordTrace (prefixWord ++ tailWord_783000) baseStart_783000 baseEnd_783000 := by
    simpa [prefixWord, tailWord_783000, baseEnd_783000] using wordTrace_append hprefix tailTrace_783000
  have hstable : (prefixWord ++ tailWord_783000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783000).length < 2 ^ (prefixWord ++ tailWord_783000).sum := by decide
  have hdescent : baseEnd_783000 < baseStart_783000 := by decide
  rcases family_descends (prefixWord ++ tailWord_783000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783127 : List Nat := [1, 1, 3, 4, 4, 1, 1, 2, 4]
def baseStart_783127 : Nat := 118140960795 + 783127 * 2 ^ 59
def prefixEnd_783127 : Nat := 4983230072969 + 3 ^ 40 * 783127 * 2
def baseEnd_783127 : Nat := 178720250894961220315987

theorem tailTrace_783127 : CollatzResearch.WordTrace tailWord_783127 prefixEnd_783127 178720250894961220315987 := by
  unfold tailWord_783127
  simp only [CollatzResearch.WordTrace]
  refine ⟨28562988233872101288531635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19041992155914734192354423 28562988233872101288531635)
  ·
    refine ⟨42844482350808151932797453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28562988233872101288531635 42844482350808151932797453)
    ·
      refine ⟨16066680881553056974799045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42844482350808151932797453 16066680881553056974799045)
      ·
        refine ⟨3012502665291198182774821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16066680881553056974799045 3012502665291198182774821)
        ·
          refine ⟨564844249742099659270279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3012502665291198182774821 564844249742099659270279)
          ·
            refine ⟨847266374613149488905419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564844249742099659270279 847266374613149488905419)
            ·
              refine ⟨1270899561919724233358129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 847266374613149488905419 1270899561919724233358129)
              ·
                refine ⟨953174671439793175018597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1270899561919724233358129 953174671439793175018597)
                ·
                  refine ⟨178720250894961220315987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 953174671439793175018597 178720250894961220315987)
                  ·
                    rfl

theorem cell21_783127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 4].length) (baseStart_783127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_783127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_783127 prefixEnd_783127 := by exact prefixLift 783127
  have htrace : WordTrace (prefixWord ++ tailWord_783127) baseStart_783127 baseEnd_783127 := by
    simpa [prefixWord, tailWord_783127, baseEnd_783127] using wordTrace_append hprefix tailTrace_783127
  have hstable : (prefixWord ++ tailWord_783127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783127).length < 2 ^ (prefixWord ++ tailWord_783127).sum := by decide
  have hdescent : baseEnd_783127 < baseStart_783127 := by decide
  rcases family_descends (prefixWord ++ tailWord_783127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783138 : List Nat := [3, 3, 1, 1, 2, 2, 1, 3, 5]
def baseStart_783138 : Nat := 118140960795 + 783138 * 2 ^ 59
def prefixEnd_783138 : Nat := 4983230072969 + 3 ^ 40 * 783138 * 2
def baseEnd_783138 : Nat := 178722761244827645632631

theorem tailTrace_783138 : CollatzResearch.WordTrace tailWord_783138 prefixEnd_783138 178722761244827645632631 := by
  unfold tailWord_783138
  simp only [CollatzResearch.WordTrace]
  refine ⟨7140847359208062541795517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19042259624554833444788045 7140847359208062541795517)
  ·
    refine ⟨2677817759703023453173319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7140847359208062541795517 2677817759703023453173319)
    ·
      refine ⟨4016726639554535179759979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2677817759703023453173319 4016726639554535179759979)
      ·
        refine ⟨6025089959331802769639969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4016726639554535179759979 6025089959331802769639969)
        ·
          refine ⟨4518817469498852077229977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6025089959331802769639969 4518817469498852077229977)
          ·
            refine ⟨3389113102124139057922483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4518817469498852077229977 3389113102124139057922483)
            ·
              refine ⟨5083669653186208586883725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3389113102124139057922483 5083669653186208586883725)
              ·
                refine ⟨1906376119944828220081397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5083669653186208586883725 1906376119944828220081397)
                ·
                  refine ⟨178722761244827645632631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1906376119944828220081397 178722761244827645632631)
                  ·
                    rfl

theorem cell21_783138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_783138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_783138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_783138 prefixEnd_783138 := by exact prefixLift 783138
  have htrace : WordTrace (prefixWord ++ tailWord_783138) baseStart_783138 baseEnd_783138 := by
    simpa [prefixWord, tailWord_783138, baseEnd_783138] using wordTrace_append hprefix tailTrace_783138
  have hstable : (prefixWord ++ tailWord_783138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783138).length < 2 ^ (prefixWord ++ tailWord_783138).sum := by decide
  have hdescent : baseEnd_783138 < baseStart_783138 := by decide
  rcases family_descends (prefixWord ++ tailWord_783138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783152 : List Nat := [2, 1, 1, 1, 2, 2, 1, 7, 4]
def baseStart_783152 : Nat := 118140960795 + 783152 * 2 ^ 59
def prefixEnd_783152 : Nat := 4983230072969 + 3 ^ 40 * 783152 * 2
def baseEnd_783152 : Nat := 178725956235566732399269

theorem tailTrace_783152 : CollatzResearch.WordTrace tailWord_783152 prefixEnd_783152 178725956235566732399269 := by
  unfold tailWord_783152
  simp only [CollatzResearch.WordTrace]
  refine ⟨14281950029390765279095855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19042600039187687038794473 14281950029390765279095855)
  ·
    refine ⟨21422925044086147918643783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14281950029390765279095855 21422925044086147918643783)
    ·
      refine ⟨32134387566129221877965675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21422925044086147918643783 32134387566129221877965675)
      ·
        refine ⟨48201581349193832816948513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32134387566129221877965675 48201581349193832816948513)
        ·
          refine ⟨36151186011895374612711385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48201581349193832816948513 36151186011895374612711385)
          ·
            refine ⟨27113389508921530959533539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36151186011895374612711385 27113389508921530959533539)
            ·
              refine ⟨40670084263382296439300309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27113389508921530959533539 40670084263382296439300309)
              ·
                refine ⟨953205099923022572796101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 40670084263382296439300309 953205099923022572796101)
                ·
                  refine ⟨178725956235566732399269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 953205099923022572796101 178725956235566732399269)
                  ·
                    rfl

theorem cell21_783152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 4].length) (baseStart_783152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_783152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_783152 prefixEnd_783152 := by exact prefixLift 783152
  have htrace : WordTrace (prefixWord ++ tailWord_783152) baseStart_783152 baseEnd_783152 := by
    simpa [prefixWord, tailWord_783152, baseEnd_783152] using wordTrace_append hprefix tailTrace_783152
  have hstable : (prefixWord ++ tailWord_783152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783152).length < 2 ^ (prefixWord ++ tailWord_783152).sum := by decide
  have hdescent : baseEnd_783152 < baseStart_783152 := by decide
  rcases family_descends (prefixWord ++ tailWord_783152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783158 : List Nat := [5, 1, 2, 2, 2, 2, 2, 5]
def baseStart_783158 : Nat := 118140960795 + 783158 * 2 ^ 59
def prefixEnd_783158 : Nat := 4983230072969 + 3 ^ 40 * 783158 * 2
def baseEnd_783158 : Nat := 59575775172437351766419

theorem tailTrace_783158 : CollatzResearch.WordTrace tailWord_783158 prefixEnd_783158 59575775172437351766419 := by
  unfold tailWord_783158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1785257431047487098931883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19042745931173195721940085 1785257431047487098931883)
  ·
    refine ⟨2677886146571230648397825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1785257431047487098931883 2677886146571230648397825)
    ·
      refine ⟨2008414609928422986298369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2677886146571230648397825 2008414609928422986298369)
      ·
        refine ⟨1506310957446317239723777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2008414609928422986298369 1506310957446317239723777)
        ·
          refine ⟨1129733218084737929792833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1506310957446317239723777 1129733218084737929792833)
          ·
            refine ⟨847299913563553447344625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1129733218084737929792833 847299913563553447344625)
            ·
              refine ⟨635474935172665085508469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 847299913563553447344625 635474935172665085508469)
              ·
                refine ⟨59575775172437351766419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 635474935172665085508469 59575775172437351766419)
                ·
                  rfl

theorem cell21_783158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_783158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_783158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_783158 prefixEnd_783158 := by exact prefixLift 783158
  have htrace : WordTrace (prefixWord ++ tailWord_783158) baseStart_783158 baseEnd_783158 := by
    simpa [prefixWord, tailWord_783158, baseEnd_783158] using wordTrace_append hprefix tailTrace_783158
  have hstable : (prefixWord ++ tailWord_783158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783158).length < 2 ^ (prefixWord ++ tailWord_783158).sum := by decide
  have hdescent : baseEnd_783158 < baseStart_783158 := by decide
  rcases family_descends (prefixWord ++ tailWord_783158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783273 : List Nat := [1, 2, 1, 1, 1, 1, 7, 2, 5]
def baseStart_783273 : Nat := 118140960795 + 783273 * 2 ^ 59
def prefixEnd_783273 : Nat := 4983230072969 + 3 ^ 40 * 783273 * 2
def baseEnd_783273 : Nat := 178753570084097410882355

theorem tailTrace_783273 : CollatzResearch.WordTrace tailWord_783273 prefixEnd_783273 178753570084097410882355 := by
  unfold tailWord_783273
  simp only [CollatzResearch.WordTrace]
  refine ⟨28568313291343168223346473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19045542194228778815564315 28568313291343168223346473)
  ·
    refine ⟨21426234968507376167509855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28568313291343168223346473 21426234968507376167509855)
    ·
      refine ⟨32139352452761064251264783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21426234968507376167509855 32139352452761064251264783)
      ·
        refine ⟨48209028679141596376897175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32139352452761064251264783 48209028679141596376897175)
        ·
          refine ⟨72313543018712394565345763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48209028679141596376897175 72313543018712394565345763)
          ·
            refine ⟨108470314528068591848018645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72313543018712394565345763 108470314528068591848018645)
            ·
              refine ⟨2542272996751607621437937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 108470314528068591848018645 2542272996751607621437937)
              ·
                refine ⟨1906704747563705716078453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2542272996751607621437937 1906704747563705716078453)
                ·
                  refine ⟨178753570084097410882355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1906704747563705716078453 178753570084097410882355)
                  ·
                    rfl

theorem cell21_783273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 5].length) (baseStart_783273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_783273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_783273 prefixEnd_783273 := by exact prefixLift 783273
  have htrace : WordTrace (prefixWord ++ tailWord_783273) baseStart_783273 baseEnd_783273 := by
    simpa [prefixWord, tailWord_783273, baseEnd_783273] using wordTrace_append hprefix tailTrace_783273
  have hstable : (prefixWord ++ tailWord_783273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783273).length < 2 ^ (prefixWord ++ tailWord_783273).sum := by decide
  have hdescent : baseEnd_783273 < baseStart_783273 := by decide
  rcases family_descends (prefixWord ++ tailWord_783273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783335 : List Nat := [1, 1, 5, 2, 2, 2, 1, 7]
def baseStart_783335 : Nat := 118140960795 + 783335 * 2 ^ 59
def prefixEnd_783335 : Nat := 4983230072969 + 3 ^ 40 * 783335 * 2
def baseEnd_783335 : Nat := 59589239776266360282965

theorem tailTrace_783335 : CollatzResearch.WordTrace tailWord_783335 prefixEnd_783335 59589239776266360282965 := by
  unfold tailWord_783335
  simp only [CollatzResearch.WordTrace]
  refine ⟨28570574617118552812103459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19047049744745701874735639 28570574617118552812103459)
  ·
    refine ⟨42855861925677829218155189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28570574617118552812103459 42855861925677829218155189)
    ·
      refine ⟨4017737055532296489202049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42855861925677829218155189 4017737055532296489202049)
      ·
        refine ⟨3013302791649222366901537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4017737055532296489202049 3013302791649222366901537)
        ·
          refine ⟨2259977093736916775176153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3013302791649222366901537 2259977093736916775176153)
          ·
            refine ⟨1694982820302687581382115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2259977093736916775176153 1694982820302687581382115)
            ·
              refine ⟨2542474230454031372073173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1694982820302687581382115 2542474230454031372073173)
              ·
                refine ⟨59589239776266360282965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2542474230454031372073173 59589239776266360282965)
                ·
                  rfl

theorem cell21_783335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 7].length) (baseStart_783335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_783335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_783335 prefixEnd_783335 := by exact prefixLift 783335
  have htrace : WordTrace (prefixWord ++ tailWord_783335) baseStart_783335 baseEnd_783335 := by
    simpa [prefixWord, tailWord_783335, baseEnd_783335] using wordTrace_append hprefix tailTrace_783335
  have hstable : (prefixWord ++ tailWord_783335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783335).length < 2 ^ (prefixWord ++ tailWord_783335).sum := by decide
  have hdescent : baseEnd_783335 < baseStart_783335 := by decide
  rcases family_descends (prefixWord ++ tailWord_783335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783414 : List Nat := [5, 1, 2, 1, 1, 3, 2, 2, 4]
def baseStart_783414 : Nat := 118140960795 + 783414 * 2 ^ 59
def prefixEnd_783414 : Nat := 4983230072969 + 3 ^ 40 * 783414 * 2
def baseEnd_783414 : Nat := 178785748205112499032067

theorem tailTrace_783414 : CollatzResearch.WordTrace tailWord_783414 prefixEnd_783414 178785748205112499032067 := by
  unfold tailWord_783414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1785840998989521831514331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19048970655888232869486197 1785840998989521831514331)
  ·
    refine ⟨2678761498484282747271497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1785840998989521831514331 2678761498484282747271497)
    ·
      refine ⟨2009071123863212060453623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2678761498484282747271497 2009071123863212060453623)
      ·
        refine ⟨3013606685794818090680435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2009071123863212060453623 3013606685794818090680435)
        ·
          refine ⟨4520410028692227136020653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3013606685794818090680435 4520410028692227136020653)
          ·
            refine ⟨1695153760759585176007745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4520410028692227136020653 1695153760759585176007745)
            ·
              refine ⟨1271365320569688882005809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1695153760759585176007745 1271365320569688882005809)
              ·
                refine ⟨953523990427266661504357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1271365320569688882005809 953523990427266661504357)
                ·
                  refine ⟨178785748205112499032067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 953523990427266661504357 178785748205112499032067)
                  ·
                    rfl

theorem cell21_783414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_783414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_783414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_783414 prefixEnd_783414 := by exact prefixLift 783414
  have htrace : WordTrace (prefixWord ++ tailWord_783414) baseStart_783414 baseEnd_783414 := by
    simpa [prefixWord, tailWord_783414, baseEnd_783414] using wordTrace_append hprefix tailTrace_783414
  have hstable : (prefixWord ++ tailWord_783414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783414).length < 2 ^ (prefixWord ++ tailWord_783414).sum := by decide
  have hdescent : baseEnd_783414 < baseStart_783414 := by decide
  rcases family_descends (prefixWord ++ tailWord_783414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783442 : List Nat := [3, 2, 2, 1, 3, 2, 1, 2, 5]
def baseStart_783442 : Nat := 118140960795 + 783442 * 2 ^ 59
def prefixEnd_783442 : Nat := 4983230072969 + 3 ^ 40 * 783442 * 2
def baseEnd_783442 : Nat := 178792138186590672565343

theorem tailTrace_783442 : CollatzResearch.WordTrace tailWord_783442 prefixEnd_783442 178792138186590672565343 := by
  unfold tailWord_783442
  simp only [CollatzResearch.WordTrace]
  refine ⟨7143619306932727521562145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19049651485153940057499053 7143619306932727521562145)
  ·
    refine ⟨5357714480199545641171609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7143619306932727521562145 5357714480199545641171609)
    ·
      refine ⟨4018285860149659230878707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5357714480199545641171609 4018285860149659230878707)
      ·
        refine ⟨6027428790224488846318061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4018285860149659230878707 6027428790224488846318061)
        ·
          refine ⟨2260285796334183317369273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6027428790224488846318061 2260285796334183317369273)
          ·
            refine ⟨1695214347250637488026955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2260285796334183317369273 1695214347250637488026955)
            ·
              refine ⟨2542821520875956232040433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1695214347250637488026955 2542821520875956232040433)
              ·
                refine ⟨1907116140656967174030325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2542821520875956232040433 1907116140656967174030325)
                ·
                  refine ⟨178792138186590672565343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1907116140656967174030325 178792138186590672565343)
                  ·
                    rfl

theorem cell21_783442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_783442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_783442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_783442 prefixEnd_783442 := by exact prefixLift 783442
  have htrace : WordTrace (prefixWord ++ tailWord_783442) baseStart_783442 baseEnd_783442 := by
    simpa [prefixWord, tailWord_783442, baseEnd_783442] using wordTrace_append hprefix tailTrace_783442
  have hstable : (prefixWord ++ tailWord_783442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783442).length < 2 ^ (prefixWord ++ tailWord_783442).sum := by decide
  have hdescent : baseEnd_783442 < baseStart_783442 := by decide
  rcases family_descends (prefixWord ++ tailWord_783442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783549 : List Nat := [1, 4, 1, 2, 1, 1, 6, 1, 4]
def baseStart_783549 : Nat := 118140960795 + 783549 * 2 ^ 59
def prefixEnd_783549 : Nat := 4983230072969 + 3 ^ 40 * 783549 * 2
def baseEnd_783549 : Nat := 178816557044382264281791

theorem tailTrace_783549 : CollatzResearch.WordTrace tailWord_783549 prefixEnd_783549 178816557044382264281791 := by
  unfold tailWord_783549
  simp only [CollatzResearch.WordTrace]
  refine ⟨28578379838343267360393701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19052253225562178240262467 28578379838343267360393701)
  ·
    refine ⟨5358446219689362630073819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28578379838343267360393701 5358446219689362630073819)
    ·
      refine ⟨8037669329534043945110729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5358446219689362630073819 8037669329534043945110729)
      ·
        refine ⟨6028251997150532958833047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8037669329534043945110729 6028251997150532958833047)
        ·
          refine ⟨9042377995725799438249571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6028251997150532958833047 9042377995725799438249571)
          ·
            refine ⟨13563566993588699157374357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9042377995725799438249571 13563566993588699157374357)
            ·
              refine ⟨635792202824470273001923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13563566993588699157374357 635792202824470273001923)
              ·
                refine ⟨953688304236705409502885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635792202824470273001923 953688304236705409502885)
                ·
                  refine ⟨178816557044382264281791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 953688304236705409502885 178816557044382264281791)
                  ·
                    rfl

theorem cell21_783549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_783549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_783549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_783549 prefixEnd_783549 := by exact prefixLift 783549
  have htrace : WordTrace (prefixWord ++ tailWord_783549) baseStart_783549 baseEnd_783549 := by
    simpa [prefixWord, tailWord_783549, baseEnd_783549] using wordTrace_append hprefix tailTrace_783549
  have hstable : (prefixWord ++ tailWord_783549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783549).length < 2 ^ (prefixWord ++ tailWord_783549).sum := by decide
  have hdescent : baseEnd_783549 < baseStart_783549 := by decide
  rcases family_descends (prefixWord ++ tailWord_783549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783653 : List Nat := [1, 3, 1, 2, 4, 1, 1, 3, 5]
def baseStart_783653 : Nat := 118140960795 + 783653 * 2 ^ 59
def prefixEnd_783653 : Nat := 4983230072969 + 3 ^ 40 * 783653 * 2
def baseEnd_783653 : Nat := 178840291261301194548245

theorem tailTrace_783653 : CollatzResearch.WordTrace tailWord_783653 prefixEnd_783653 178840291261301194548245 := by
  unfold tailWord_783653
  simp only [CollatzResearch.WordTrace]
  refine ⟨28582173029966493122179613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19054782019977662081453075 28582173029966493122179613)
  ·
    refine ⟨10718314886237434920817355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28582173029966493122179613 10718314886237434920817355)
    ·
      refine ⟨16077472329356152381226033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10718314886237434920817355 16077472329356152381226033)
      ·
        refine ⟨12058104247017114285919525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16077472329356152381226033 12058104247017114285919525)
        ·
          refine ⟨2260894546315708928609911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12058104247017114285919525 2260894546315708928609911)
          ·
            refine ⟨3391341819473563392914867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2260894546315708928609911 3391341819473563392914867)
            ·
              refine ⟨5087012729210345089372301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3391341819473563392914867 5087012729210345089372301)
              ·
                refine ⟨1907629773453879408514613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5087012729210345089372301 1907629773453879408514613)
                ·
                  refine ⟨178840291261301194548245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1907629773453879408514613 178840291261301194548245)
                  ·
                    rfl

theorem cell21_783653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_783653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_783653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_783653 prefixEnd_783653 := by exact prefixLift 783653
  have htrace : WordTrace (prefixWord ++ tailWord_783653) baseStart_783653 baseEnd_783653 := by
    simpa [prefixWord, tailWord_783653, baseEnd_783653] using wordTrace_append hprefix tailTrace_783653
  have hstable : (prefixWord ++ tailWord_783653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783653).length < 2 ^ (prefixWord ++ tailWord_783653).sum := by decide
  have hdescent : baseEnd_783653 < baseStart_783653 := by decide
  rcases family_descends (prefixWord ++ tailWord_783653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783673 : List Nat := [1, 2, 1, 6, 3, 1, 2, 5]
def baseStart_783673 : Nat := 118140960795 + 783673 * 2 ^ 59
def prefixEnd_783673 : Nat := 4983230072969 + 3 ^ 40 * 783673 * 2
def baseEnd_783673 : Nat := 59614951844595201404957

theorem tailTrace_783673 : CollatzResearch.WordTrace tailWord_783673 prefixEnd_783673 59614951844595201404957 := by
  unfold tailWord_783673
  simp only [CollatzResearch.WordTrace]
  refine ⟨28582902489894036537907673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19055268326596024358605115 28582902489894036537907673)
  ·
    refine ⟨21437176867420527403430755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28582902489894036537907673 21437176867420527403430755)
    ·
      refine ⟨32155765301130791105146133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21437176867420527403430755 32155765301130791105146133)
      ·
        refine ⟨1507301498490505833053725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32155765301130791105146133 1507301498490505833053725)
        ·
          refine ⟨565238061933939687395147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1507301498490505833053725 565238061933939687395147)
          ·
            refine ⟨847857092900909531092721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565238061933939687395147 847857092900909531092721)
            ·
              refine ⟨635892819675682148319541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 847857092900909531092721 635892819675682148319541)
              ·
                refine ⟨59614951844595201404957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 635892819675682148319541 59614951844595201404957)
                ·
                  rfl

theorem cell21_783673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 5].length) (baseStart_783673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_783673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_783673 prefixEnd_783673 := by exact prefixLift 783673
  have htrace : WordTrace (prefixWord ++ tailWord_783673) baseStart_783673 baseEnd_783673 := by
    simpa [prefixWord, tailWord_783673, baseEnd_783673] using wordTrace_append hprefix tailTrace_783673
  have hstable : (prefixWord ++ tailWord_783673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783673).length < 2 ^ (prefixWord ++ tailWord_783673).sum := by decide
  have hdescent : baseEnd_783673 < baseStart_783673 := by decide
  rcases family_descends (prefixWord ++ tailWord_783673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783687 : List Nat := [1, 1, 4, 1, 2, 5, 1, 3, 3]
def baseStart_783687 : Nat := 118140960795 + 783687 * 2 ^ 59
def prefixEnd_783687 : Nat := 4983230072969 + 3 ^ 40 * 783687 * 2
def baseEnd_783687 : Nat := 178848050524524690981509

theorem tailTrace_783687 : CollatzResearch.WordTrace tailWord_783687 prefixEnd_783687 178848050524524690981509 := by
  unfold tailWord_783687
  simp only [CollatzResearch.WordTrace]
  refine ⟨28583413111843316928917315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19055608741228877952611543 28583413111843316928917315)
  ·
    refine ⟨42875119667764975393375973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28583413111843316928917315 42875119667764975393375973)
    ·
      refine ⟨8039084937705932886257995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42875119667764975393375973 8039084937705932886257995)
      ·
        refine ⟨12058627406558899329386993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8039084937705932886257995 12058627406558899329386993)
        ·
          refine ⟨9043970554919174497040245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12058627406558899329386993 9043970554919174497040245)
          ·
            refine ⟨847872239523672609097523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9043970554919174497040245 847872239523672609097523)
            ·
              refine ⟨1271808359285508913646285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 847872239523672609097523 1271808359285508913646285)
              ·
                refine ⟨476928134732065842617357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1271808359285508913646285 476928134732065842617357)
                ·
                  refine ⟨178848050524524690981509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 476928134732065842617357 178848050524524690981509)
                  ·
                    rfl

theorem cell21_783687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 3, 3].length) (baseStart_783687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_783687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_783687 prefixEnd_783687 := by exact prefixLift 783687
  have htrace : WordTrace (prefixWord ++ tailWord_783687) baseStart_783687 baseEnd_783687 := by
    simpa [prefixWord, tailWord_783687, baseEnd_783687] using wordTrace_append hprefix tailTrace_783687
  have hstable : (prefixWord ++ tailWord_783687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783687).length < 2 ^ (prefixWord ++ tailWord_783687).sum := by decide
  have hdescent : baseEnd_783687 < baseStart_783687 := by decide
  rcases family_descends (prefixWord ++ tailWord_783687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783788 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 7]
def baseStart_783788 : Nat := 118140960795 + 783788 * 2 ^ 59
def prefixEnd_783788 : Nat := 4983230072969 + 3 ^ 40 * 783788 * 2
def baseEnd_783788 : Nat := 178871100100570959797969

theorem tailTrace_783788 : CollatzResearch.WordTrace tailWord_783788 prefixEnd_783788 178871100100570959797969 := by
  unfold tailWord_783788
  simp only [CollatzResearch.WordTrace]
  refine ⟨14293548442238705589172009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19058064589651607452229345 14293548442238705589172009)
  ·
    refine ⟨10720161331679029191879007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14293548442238705589172009 10720161331679029191879007)
    ·
      refine ⟨16080241997518543787818511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10720161331679029191879007 16080241997518543787818511)
      ·
        refine ⟨24120362996277815681727767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16080241997518543787818511 24120362996277815681727767)
        ·
          refine ⟨36180544494416723522591651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24120362996277815681727767 36180544494416723522591651)
          ·
            refine ⟨54270816741625085283887477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36180544494416723522591651 54270816741625085283887477)
            ·
              refine ⟨5087889069527351745364451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54270816741625085283887477 5087889069527351745364451)
              ·
                refine ⟨7631833604291027618046677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5087889069527351745364451 7631833604291027618046677)
                ·
                  refine ⟨178871100100570959797969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7631833604291027618046677 178871100100570959797969)
                  ·
                    rfl

theorem cell21_783788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_783788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_783788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_783788 prefixEnd_783788 := by exact prefixLift 783788
  have htrace : WordTrace (prefixWord ++ tailWord_783788) baseStart_783788 baseEnd_783788 := by
    simpa [prefixWord, tailWord_783788, baseEnd_783788] using wordTrace_append hprefix tailTrace_783788
  have hstable : (prefixWord ++ tailWord_783788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783788).length < 2 ^ (prefixWord ++ tailWord_783788).sum := by decide
  have hdescent : baseEnd_783788 < baseStart_783788 := by decide
  rcases family_descends (prefixWord ++ tailWord_783788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783822 : List Nat := [4, 1, 1, 1, 2, 1, 4, 4, 3]
def baseStart_783822 : Nat := 118140960795 + 783822 * 2 ^ 59
def prefixEnd_783822 : Nat := 4983230072969 + 3 ^ 40 * 783822 * 2
def baseEnd_783822 : Nat := 178878859363794456231233

theorem tailTrace_783822 : CollatzResearch.WordTrace tailWord_783822 prefixEnd_783822 178878859363794456231233 := by
  unfold tailWord_783822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3573542120794279373135215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19058891310902823323387813 3573542120794279373135215)
  ·
    refine ⟨5360313181191419059702823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3573542120794279373135215 5360313181191419059702823)
    ·
      refine ⟨8040469771787128589554235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5360313181191419059702823 8040469771787128589554235)
      ·
        refine ⟨12060704657680692884331353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8040469771787128589554235 12060704657680692884331353)
        ·
          refine ⟨9045528493260519663248515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12060704657680692884331353 9045528493260519663248515)
          ·
            refine ⟨13568292739890779494872773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9045528493260519663248515 13568292739890779494872773)
            ·
              refine ⟨2544054888729521155288645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13568292739890779494872773 2544054888729521155288645)
              ·
                refine ⟨477010291636785216616621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2544054888729521155288645 477010291636785216616621)
                ·
                  refine ⟨178878859363794456231233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 477010291636785216616621 178878859363794456231233)
                  ·
                    rfl

theorem cell21_783822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_783822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_783822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_783822 prefixEnd_783822 := by exact prefixLift 783822
  have htrace : WordTrace (prefixWord ++ tailWord_783822) baseStart_783822 baseEnd_783822 := by
    simpa [prefixWord, tailWord_783822, baseEnd_783822] using wordTrace_append hprefix tailTrace_783822
  have hstable : (prefixWord ++ tailWord_783822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783822).length < 2 ^ (prefixWord ++ tailWord_783822).sum := by decide
  have hdescent : baseEnd_783822 < baseStart_783822 := by decide
  rcases family_descends (prefixWord ++ tailWord_783822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783926 : List Nat := [5, 1, 2, 1, 12]
def baseStart_783926 : Nat := 118140960795 + 783926 * 2 ^ 59
def prefixEnd_783926 : Nat := 4983230072969 + 3 ^ 40 * 783926 * 2
def baseEnd_783926 : Nat := 2208673994823622055527

theorem tailTrace_783926 : CollatzResearch.WordTrace tailWord_783926 prefixEnd_783926 2208673994823622055527 := by
  unfold tailWord_783926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1787008134873591296679227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19061420105318307164578421 1787008134873591296679227)
  ·
    refine ⟨2680512202310386945018841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1787008134873591296679227 2680512202310386945018841)
    ·
      refine ⟨2010384151732790208764131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2680512202310386945018841 2010384151732790208764131)
      ·
        refine ⟨3015576227599185313146197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2010384151732790208764131 3015576227599185313146197)
        ·
          refine ⟨2208673994823622055527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3015576227599185313146197 2208673994823622055527)
          ·
            rfl

theorem cell21_783926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 12].length) (baseStart_783926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_783926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_783926 prefixEnd_783926 := by exact prefixLift 783926
  have htrace : WordTrace (prefixWord ++ tailWord_783926) baseStart_783926 baseEnd_783926 := by
    simpa [prefixWord, tailWord_783926, baseEnd_783926] using wordTrace_append hprefix tailTrace_783926
  have hstable : (prefixWord ++ tailWord_783926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783926).length < 2 ^ (prefixWord ++ tailWord_783926).sum := by decide
  have hdescent : baseEnd_783926 < baseStart_783926 := by decide
  rcases family_descends (prefixWord ++ tailWord_783926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783932 : List Nat := [2, 2, 2, 2, 4, 2, 2, 2, 3]
def baseStart_783932 : Nat := 118140960795 + 783932 * 2 ^ 59
def prefixEnd_783932 : Nat := 4983230072969 + 3 ^ 40 * 783932 * 2
def baseEnd_783932 : Nat := 178903962862458709397675

theorem tailTrace_783932 : CollatzResearch.WordTrace tailWord_783932 prefixEnd_783932 178903962862458709397675 := by
  unfold tailWord_783932
  simp only [CollatzResearch.WordTrace]
  refine ⟨14296174497977861885793025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19061565997303815847724033 14296174497977861885793025)
  ·
    refine ⟨10722130873483396414344769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14296174497977861885793025 10722130873483396414344769)
    ·
      refine ⟨8041598155112547310758577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10722130873483396414344769 8041598155112547310758577)
      ·
        refine ⟨6031198616334410483068933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8041598155112547310758577 6031198616334410483068933)
        ·
          refine ⟨1130849740562701965575425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6031198616334410483068933 1130849740562701965575425)
          ·
            refine ⟨848137305422026474181569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1130849740562701965575425 848137305422026474181569)
            ·
              refine ⟨636102979066519855636177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 848137305422026474181569 636102979066519855636177)
              ·
                refine ⟨477077234299889891727133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 636102979066519855636177 477077234299889891727133)
                ·
                  refine ⟨178903962862458709397675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 477077234299889891727133 178903962862458709397675)
                  ·
                    rfl

theorem cell21_783932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2, 3].length) (baseStart_783932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_783932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_783932 prefixEnd_783932 := by exact prefixLift 783932
  have htrace : WordTrace (prefixWord ++ tailWord_783932) baseStart_783932 baseEnd_783932 := by
    simpa [prefixWord, tailWord_783932, baseEnd_783932] using wordTrace_append hprefix tailTrace_783932
  have hstable : (prefixWord ++ tailWord_783932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783932).length < 2 ^ (prefixWord ++ tailWord_783932).sum := by decide
  have hdescent : baseEnd_783932 < baseStart_783932 := by decide
  rcases family_descends (prefixWord ++ tailWord_783932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783943 : List Nat := [1, 1, 4, 1, 5, 2, 1, 6]
def baseStart_783943 : Nat := 118140960795 + 783943 * 2 ^ 59
def prefixEnd_783943 : Nat := 4983230072969 + 3 ^ 40 * 783943 * 2
def baseEnd_783943 : Nat := 59635491070775044904773

theorem tailTrace_783943 : CollatzResearch.WordTrace tailWord_783943 prefixEnd_783943 59635491070775044904773 := by
  unfold tailWord_783943
  simp only [CollatzResearch.WordTrace]
  refine ⟨28592750198915872650236483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19061833465943915100157655 28592750198915872650236483)
  ·
    refine ⟨42889125298373808975354725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28592750198915872650236483 42889125298373808975354725)
    ·
      refine ⟨8041710993445089182879011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42889125298373808975354725 8041710993445089182879011)
      ·
        refine ⟨12062566490167633774318517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8041710993445089182879011 12062566490167633774318517)
        ·
          refine ⟨1130865608453215666342361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12062566490167633774318517 1130865608453215666342361)
          ·
            refine ⟨848149206339911749756771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1130865608453215666342361 848149206339911749756771)
            ·
              refine ⟨1272223809509867624635157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 848149206339911749756771 1272223809509867624635157)
              ·
                refine ⟨59635491070775044904773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1272223809509867624635157 59635491070775044904773)
                ·
                  rfl

theorem cell21_783943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 6].length) (baseStart_783943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_783943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_783943 prefixEnd_783943 := by exact prefixLift 783943
  have htrace : WordTrace (prefixWord ++ tailWord_783943) baseStart_783943 baseEnd_783943 := by
    simpa [prefixWord, tailWord_783943, baseEnd_783943] using wordTrace_append hprefix tailTrace_783943
  have hstable : (prefixWord ++ tailWord_783943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783943).length < 2 ^ (prefixWord ++ tailWord_783943).sum := by decide
  have hdescent : baseEnd_783943 < baseStart_783943 := by decide
  rcases family_descends (prefixWord ++ tailWord_783943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784047 : List Nat := [1, 1, 2, 1, 2, 4, 2, 4, 4]
def baseStart_784047 : Nat := 118140960795 + 784047 * 2 ^ 59
def prefixEnd_784047 : Nat := 4983230072969 + 3 ^ 40 * 784047 * 2
def baseEnd_784047 : Nat := 178930207429244064980773

theorem tailTrace_784047 : CollatzResearch.WordTrace tailWord_784047 prefixEnd_784047 178930207429244064980773 := by
  unfold tailWord_784047
  simp only [CollatzResearch.WordTrace]
  refine ⟨28596543390539098412022395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19064362260359398941348263 28596543390539098412022395)
  ·
    refine ⟨42894815085808647618033593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28596543390539098412022395 42894815085808647618033593)
    ·
      refine ⟨32171111314356485713525195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42894815085808647618033593 32171111314356485713525195)
      ·
        refine ⟨48256666971534728570287793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32171111314356485713525195 48256666971534728570287793)
        ·
          refine ⟨36192500228651046427715845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48256666971534728570287793 36192500228651046427715845)
          ·
            refine ⟨6786093792872071205196721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36192500228651046427715845 6786093792872071205196721)
            ·
              refine ⟨5089570344654053403897541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6786093792872071205196721 5089570344654053403897541)
              ·
                refine ⟨954294439622635013230789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5089570344654053403897541 954294439622635013230789)
                ·
                  refine ⟨178930207429244064980773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 954294439622635013230789 178930207429244064980773)
                  ·
                    rfl

theorem cell21_784047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 4].length) (baseStart_784047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_784047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_784047 prefixEnd_784047 := by exact prefixLift 784047
  have htrace : WordTrace (prefixWord ++ tailWord_784047) baseStart_784047 baseEnd_784047 := by
    simpa [prefixWord, tailWord_784047, baseEnd_784047] using wordTrace_append hprefix tailTrace_784047
  have hstable : (prefixWord ++ tailWord_784047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784047).length < 2 ^ (prefixWord ++ tailWord_784047).sum := by decide
  have hdescent : baseEnd_784047 < baseStart_784047 := by decide
  rcases family_descends (prefixWord ++ tailWord_784047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784126 : List Nat := [4, 2, 2, 1, 3, 1, 1, 2, 5]
def baseStart_784126 : Nat := 118140960795 + 784126 * 2 ^ 59
def prefixEnd_784126 : Nat := 4983230072969 + 3 ^ 40 * 784126 * 2
def baseEnd_784126 : Nat := 178948236305557483163945

theorem tailTrace_784126 : CollatzResearch.WordTrace tailWord_784126 prefixEnd_784126 178948236305557483163945 := by
  unfold tailWord_784126
  simp only [CollatzResearch.WordTrace]
  refine ⟨3574928094656611863018529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19066283171501929936098821 3574928094656611863018529)
  ·
    refine ⟨2681196070992458897263897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3574928094656611863018529 2681196070992458897263897)
    ·
      refine ⟨2010897053244344172947923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2681196070992458897263897 2010897053244344172947923)
      ·
        refine ⟨3016345579866516259421885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2010897053244344172947923 3016345579866516259421885)
        ·
          refine ⟨1131129592449943597283207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3016345579866516259421885 1131129592449943597283207)
          ·
            refine ⟨1696694388674915395924811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1131129592449943597283207 1696694388674915395924811)
            ·
              refine ⟨2545041583012373093887217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1696694388674915395924811 2545041583012373093887217)
              ·
                refine ⟨1908781187259279820415413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2545041583012373093887217 1908781187259279820415413)
                ·
                  refine ⟨178948236305557483163945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1908781187259279820415413 178948236305557483163945)
                  ·
                    rfl

theorem cell21_784126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_784126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_784126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_784126 prefixEnd_784126 := by exact prefixLift 784126
  have htrace : WordTrace (prefixWord ++ tailWord_784126) baseStart_784126 baseEnd_784126 := by
    simpa [prefixWord, tailWord_784126, baseEnd_784126] using wordTrace_append hprefix tailTrace_784126
  have hstable : (prefixWord ++ tailWord_784126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784126).length < 2 ^ (prefixWord ++ tailWord_784126).sum := by decide
  have hdescent : baseEnd_784126 < baseStart_784126 := by decide
  rcases family_descends (prefixWord ++ tailWord_784126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784174 : List Nat := [4, 1, 3, 2, 2, 1, 3, 1, 4]
def baseStart_784174 : Nat := 118140960795 + 784174 * 2 ^ 59
def prefixEnd_784174 : Nat := 4983230072969 + 3 ^ 40 * 784174 * 2
def baseEnd_784174 : Nat := 178959190559520066363847

theorem tailTrace_784174 : CollatzResearch.WordTrace tailWord_784174 prefixEnd_784174 178959190559520066363847 := by
  unfold tailWord_784174
  simp only [CollatzResearch.WordTrace]
  refine ⟨3575146932634874887736947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19067450307385999401263717 3575146932634874887736947)
  ·
    refine ⟨5362720398952312331605421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3575146932634874887736947 5362720398952312331605421)
    ·
      refine ⟨2011020149607117124352033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5362720398952312331605421 2011020149607117124352033)
      ·
        refine ⟨1508265112205337843264025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2011020149607117124352033 1508265112205337843264025)
        ·
          refine ⟨1131198834154003382448019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1508265112205337843264025 1131198834154003382448019)
          ·
            refine ⟨1696798251231005073672029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1131198834154003382448019 1696798251231005073672029)
            ·
              refine ⟨636299344211626902627011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1696798251231005073672029 636299344211626902627011)
              ·
                refine ⟨954449016317440353940517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 636299344211626902627011 954449016317440353940517)
                ·
                  refine ⟨178959190559520066363847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 954449016317440353940517 178959190559520066363847)
                  ·
                    rfl

theorem cell21_784174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_784174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_784174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_784174 prefixEnd_784174 := by exact prefixLift 784174
  have htrace : WordTrace (prefixWord ++ tailWord_784174) baseStart_784174 baseEnd_784174 := by
    simpa [prefixWord, tailWord_784174, baseEnd_784174] using wordTrace_append hprefix tailTrace_784174
  have hstable : (prefixWord ++ tailWord_784174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784174).length < 2 ^ (prefixWord ++ tailWord_784174).sum := by decide
  have hdescent : baseEnd_784174 < baseStart_784174 := by decide
  rcases family_descends (prefixWord ++ tailWord_784174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784213 : List Nat := [1, 3, 2, 2, 2, 2, 9]
def baseStart_784213 : Nat := 118140960795 + 784213 * 2 ^ 59
def prefixEnd_784213 : Nat := 4983230072969 + 3 ^ 40 * 784213 * 2
def baseEnd_784213 : Nat := 19885343432318296134863

theorem tailTrace_784213 : CollatzResearch.WordTrace tailWord_784213 prefixEnd_784213 19885343432318296134863 := by
  unfold tailWord_784213
  simp only [CollatzResearch.WordTrace]
  refine ⟨28602597907937708762565293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19068398605291805841710195 28602597907937708762565293)
  ·
    refine ⟨10725974215476640785961985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28602597907937708762565293 10725974215476640785961985)
    ·
      refine ⟨8044480661607480589471489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10725974215476640785961985 8044480661607480589471489)
      ·
        refine ⟨6033360496205610442103617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8044480661607480589471489 6033360496205610442103617)
        ·
          refine ⟨4525020372154207831577713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6033360496205610442103617 4525020372154207831577713)
          ·
            refine ⟨3393765279115655873683285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4525020372154207831577713 3393765279115655873683285)
            ·
              refine ⟨19885343432318296134863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3393765279115655873683285 19885343432318296134863)
              ·
                rfl

theorem cell21_784213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 9].length) (baseStart_784213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_784213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_784213 prefixEnd_784213 := by exact prefixLift 784213
  have htrace : WordTrace (prefixWord ++ tailWord_784213) baseStart_784213 baseEnd_784213 := by
    simpa [prefixWord, tailWord_784213, baseEnd_784213] using wordTrace_append hprefix tailTrace_784213
  have hstable : (prefixWord ++ tailWord_784213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784213).length < 2 ^ (prefixWord ++ tailWord_784213).sum := by decide
  have hdescent : baseEnd_784213 < baseStart_784213 := by decide
  rcases family_descends (prefixWord ++ tailWord_784213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784261 : List Nat := [1, 3, 1, 1, 3, 2, 2, 5, 3]
def baseStart_784261 : Nat := 118140960795 + 784261 * 2 ^ 59
def prefixEnd_784261 : Nat := 4983230072969 + 3 ^ 40 * 784261 * 2
def baseEnd_784261 : Nat := 178979045144827248413669

theorem tailTrace_784261 : CollatzResearch.WordTrace tailWord_784261 prefixEnd_784261 178979045144827248413669 := by
  unfold tailWord_784261
  simp only [CollatzResearch.WordTrace]
  refine ⟨28604348611763812960312637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19069565741175875306875091 28604348611763812960312637)
  ·
    refine ⟨10726630729411429860117239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28604348611763812960312637 10726630729411429860117239)
    ·
      refine ⟨16089946094117144790175859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10726630729411429860117239 16089946094117144790175859)
      ·
        refine ⟨24134919141175717185263789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16089946094117144790175859 24134919141175717185263789)
        ·
          refine ⟨9050594677940893944473921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24134919141175717185263789 9050594677940893944473921)
          ·
            refine ⟨6787946008455670458355441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9050594677940893944473921 6787946008455670458355441)
            ·
              refine ⟨5090959506341752843766581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6787946008455670458355441 5090959506341752843766581)
              ·
                refine ⟨477277453719539329103117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5090959506341752843766581 477277453719539329103117)
                ·
                  refine ⟨178979045144827248413669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 477277453719539329103117 178979045144827248413669)
                  ·
                    rfl

theorem cell21_784261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 5, 3].length) (baseStart_784261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_784261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_784261 prefixEnd_784261 := by exact prefixLift 784261
  have htrace : WordTrace (prefixWord ++ tailWord_784261) baseStart_784261 baseEnd_784261 := by
    simpa [prefixWord, tailWord_784261, baseEnd_784261] using wordTrace_append hprefix tailTrace_784261
  have hstable : (prefixWord ++ tailWord_784261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784261).length < 2 ^ (prefixWord ++ tailWord_784261).sum := by decide
  have hdescent : baseEnd_784261 < baseStart_784261 := by decide
  rcases family_descends (prefixWord ++ tailWord_784261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784379 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 7]
def baseStart_784379 : Nat := 118140960795 + 784379 * 2 ^ 59
def prefixEnd_784379 : Nat := 4983230072969 + 3 ^ 40 * 784379 * 2
def baseEnd_784379 : Nat := 179005974352485265446761

theorem tailTrace_784379 : CollatzResearch.WordTrace tailWord_784379 prefixEnd_784379 179005974352485265446761 := by
  unfold tailWord_784379
  simp only [CollatzResearch.WordTrace]
  refine ⟨28608652425336319113108191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19072434950224212742072127 28608652425336319113108191)
  ·
    refine ⟨42912978638004478669662287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28608652425336319113108191 42912978638004478669662287)
    ·
      refine ⟨64369467957006718004493431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42912978638004478669662287 64369467957006718004493431)
      ·
        refine ⟨96554201935510077006740147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64369467957006718004493431 96554201935510077006740147)
        ·
          refine ⟨144831302903265115510110221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96554201935510077006740147 144831302903265115510110221)
          ·
            refine ⟨54311738588724418316291333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144831302903265115510110221 54311738588724418316291333)
            ·
              refine ⟨10183450985385828434304625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54311738588724418316291333 10183450985385828434304625)
              ·
                refine ⟨7637588239039371325728469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10183450985385828434304625 7637588239039371325728469)
                ·
                  refine ⟨179005974352485265446761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7637588239039371325728469 179005974352485265446761)
                  ·
                    rfl

theorem cell21_784379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 7].length) (baseStart_784379 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_784379 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_784379 prefixEnd_784379 := by exact prefixLift 784379
  have htrace : WordTrace (prefixWord ++ tailWord_784379) baseStart_784379 baseEnd_784379 := by
    simpa [prefixWord, tailWord_784379, baseEnd_784379] using wordTrace_append hprefix tailTrace_784379
  have hstable : (prefixWord ++ tailWord_784379).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784379).length < 2 ^ (prefixWord ++ tailWord_784379).sum := by decide
  have hdescent : baseEnd_784379 < baseStart_784379 := by decide
  rcases family_descends (prefixWord ++ tailWord_784379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784382 : List Nat := [4, 2, 2, 2, 1, 1, 9]
def baseStart_784382 : Nat := 118140960795 + 784382 * 2 ^ 59
def prefixEnd_784382 : Nat := 4983230072969 + 3 ^ 40 * 784382 * 2
def baseEnd_784382 : Nat := 19889628777039769655195

theorem tailTrace_784382 : CollatzResearch.WordTrace tailWord_784382 prefixEnd_784382 19889628777039769655195 := by
  unfold tailWord_784382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3576095230540681328183425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19072507896216967083644933 3576095230540681328183425)
  ·
    refine ⟨2682071422905510996137569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3576095230540681328183425 2682071422905510996137569)
    ·
      refine ⟨2011553567179133247103177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2682071422905510996137569 2011553567179133247103177)
      ·
        refine ⟨1508665175384349935327383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2011553567179133247103177 1508665175384349935327383)
        ·
          refine ⟨2262997763076524902991075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1508665175384349935327383 2262997763076524902991075)
          ·
            refine ⟨3394496644614787354486613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2262997763076524902991075 3394496644614787354486613)
            ·
              refine ⟨19889628777039769655195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3394496644614787354486613 19889628777039769655195)
              ·
                rfl

theorem cell21_784382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 9].length) (baseStart_784382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_784382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_784382 prefixEnd_784382 := by exact prefixLift 784382
  have htrace : WordTrace (prefixWord ++ tailWord_784382) baseStart_784382 baseEnd_784382 := by
    simpa [prefixWord, tailWord_784382, baseEnd_784382] using wordTrace_append hprefix tailTrace_784382
  have hstable : (prefixWord ++ tailWord_784382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784382).length < 2 ^ (prefixWord ++ tailWord_784382).sum := by decide
  have hdescent : baseEnd_784382 < baseStart_784382 := by decide
  rcases family_descends (prefixWord ++ tailWord_784382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784388 : List Nat := [2, 3, 2, 4, 1, 1, 3, 2, 3]
def baseStart_784388 : Nat := 118140960795 + 784388 * 2 ^ 59
def prefixEnd_784388 : Nat := 4983230072969 + 3 ^ 40 * 784388 * 2
def baseEnd_784388 : Nat := 179008028275103249796743

theorem tailTrace_784388 : CollatzResearch.WordTrace tailWord_784388 prefixEnd_784388 179008028275103249796743 := by
  unfold tailWord_784388
  simp only [CollatzResearch.WordTrace]
  refine ⟨14304490341151856825092909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19072653788202475766790545 14304490341151856825092909)
  ·
    refine ⟨5364183877931946309409841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14304490341151856825092909 5364183877931946309409841)
    ·
      refine ⟨4023137908448959732057381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5364183877931946309409841 4023137908448959732057381)
      ·
        refine ⟨754338357834179949760759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4023137908448959732057381 754338357834179949760759)
        ·
          refine ⟨1131507536751269924641139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754338357834179949760759 1131507536751269924641139)
          ·
            refine ⟨1697261305126904886961709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1131507536751269924641139 1697261305126904886961709)
            ·
              refine ⟨636472989422589332610641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1697261305126904886961709 636472989422589332610641)
              ·
                refine ⟨477354742066941999457981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 636472989422589332610641 477354742066941999457981)
                ·
                  refine ⟨179008028275103249796743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 477354742066941999457981 179008028275103249796743)
                  ·
                    rfl

theorem cell21_784388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_784388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_784388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_784388 prefixEnd_784388 := by exact prefixLift 784388
  have htrace : WordTrace (prefixWord ++ tailWord_784388) baseStart_784388 baseEnd_784388 := by
    simpa [prefixWord, tailWord_784388, baseEnd_784388] using wordTrace_append hprefix tailTrace_784388
  have hstable : (prefixWord ++ tailWord_784388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784388).length < 2 ^ (prefixWord ++ tailWord_784388).sum := by decide
  have hdescent : baseEnd_784388 < baseStart_784388 := by decide
  rcases family_descends (prefixWord ++ tailWord_784388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784441 : List Nat := [1, 2, 1, 5, 3, 9]
def baseStart_784441 : Nat := 118140960795 + 784441 * 2 ^ 59
def prefixEnd_784441 : Nat := 4983230072969 + 3 ^ 40 * 784441 * 2
def baseEnd_784441 : Nat := 6630374948043960570863

theorem tailTrace_784441 : CollatzResearch.WordTrace tailWord_784441 prefixEnd_784441 6630374948043960570863 := by
  unfold tailWord_784441
  simp only [CollatzResearch.WordTrace]
  refine ⟨28610913751111703701865177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19073942500741135801243451 28610913751111703701865177)
  ·
    refine ⟨21458185313333777776398883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28610913751111703701865177 21458185313333777776398883)
    ·
      refine ⟨32187277970000666664598325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21458185313333777776398883 32187277970000666664598325)
      ·
        refine ⟨3017557309687562499806093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32187277970000666664598325 3017557309687562499806093)
        ·
          refine ⟨1131583991132835937427285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3017557309687562499806093 1131583991132835937427285)
          ·
            refine ⟨6630374948043960570863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1131583991132835937427285 6630374948043960570863)
            ·
              rfl

theorem cell21_784441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 9].length) (baseStart_784441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_784441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_784441 prefixEnd_784441 := by exact prefixLift 784441
  have htrace : WordTrace (prefixWord ++ tailWord_784441) baseStart_784441 baseEnd_784441 := by
    simpa [prefixWord, tailWord_784441, baseEnd_784441] using wordTrace_append hprefix tailTrace_784441
  have hstable : (prefixWord ++ tailWord_784441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784441).length < 2 ^ (prefixWord ++ tailWord_784441).sum := by decide
  have hdescent : baseEnd_784441 < baseStart_784441 := by decide
  rcases family_descends (prefixWord ++ tailWord_784441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784472 : List Nat := [2, 1, 2, 2, 1, 5, 1, 2, 5]
def baseStart_784472 : Nat := 118140960795 + 784472 * 2 ^ 59
def prefixEnd_784472 : Nat := 4983230072969 + 3 ^ 40 * 784472 * 2
def baseEnd_784472 : Nat := 179027198219537770396571

theorem tailTrace_784472 : CollatzResearch.WordTrace tailWord_784472 prefixEnd_784472 179027198219537770396571 := by
  unfold tailWord_784472
  simp only [CollatzResearch.WordTrace]
  refine ⟨14306022206999697998121835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19074696275999597330829113 14306022206999697998121835)
  ·
    refine ⟨21459033310499546997182753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14306022206999697998121835 21459033310499546997182753)
    ·
      refine ⟨16094274982874660247887065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21459033310499546997182753 16094274982874660247887065)
      ·
        refine ⟨12070706237155995185915299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16094274982874660247887065 12070706237155995185915299)
        ·
          refine ⟨18106059355733992778872949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12070706237155995185915299 18106059355733992778872949)
          ·
            refine ⟨1697443064600061823019339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18106059355733992778872949 1697443064600061823019339)
            ·
              refine ⟨2546164596900092734529009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1697443064600061823019339 2546164596900092734529009)
              ·
                refine ⟨1909623447675069550896757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2546164596900092734529009 1909623447675069550896757)
                ·
                  refine ⟨179027198219537770396571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1909623447675069550896757 179027198219537770396571)
                  ·
                    rfl

theorem cell21_784472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 5].length) (baseStart_784472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_784472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_784472 prefixEnd_784472 := by exact prefixLift 784472
  have htrace : WordTrace (prefixWord ++ tailWord_784472) baseStart_784472 baseEnd_784472 := by
    simpa [prefixWord, tailWord_784472, baseEnd_784472] using wordTrace_append hprefix tailTrace_784472
  have hstable : (prefixWord ++ tailWord_784472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784472).length < 2 ^ (prefixWord ++ tailWord_784472).sum := by decide
  have hdescent : baseEnd_784472 < baseStart_784472 := by decide
  rcases family_descends (prefixWord ++ tailWord_784472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784489 : List Nat := [1, 2, 1, 1, 1, 5, 4, 3, 3]
def baseStart_784489 : Nat := 118140960795 + 784489 * 2 ^ 59
def prefixEnd_784489 : Nat := 4983230072969 + 3 ^ 40 * 784489 * 2
def baseEnd_784489 : Nat := 179031077851149518613203

theorem tailTrace_784489 : CollatzResearch.WordTrace tailWord_784489 prefixEnd_784489 179031077851149518613203 := by
  unfold tailWord_784489
  simp only [CollatzResearch.WordTrace]
  refine ⟨28612664454937807899612521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19075109636625205266408347 28612664454937807899612521)
  ·
    refine ⟨21459498341203355924709391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28612664454937807899612521 21459498341203355924709391)
    ·
      refine ⟨32189247511805033887064087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21459498341203355924709391 32189247511805033887064087)
      ·
        refine ⟨48283871267707550830596131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32189247511805033887064087 48283871267707550830596131)
        ·
          refine ⟨72425806901561326245894197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48283871267707550830596131 72425806901561326245894197)
          ·
            refine ⟨6789919397021374335552581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72425806901561326245894197 6789919397021374335552581)
            ·
              refine ⟨1273109886941507687916109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6789919397021374335552581 1273109886941507687916109)
              ·
                refine ⟨477416207603065382968541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1273109886941507687916109 477416207603065382968541)
                ·
                  refine ⟨179031077851149518613203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 477416207603065382968541 179031077851149518613203)
                  ·
                    rfl

theorem cell21_784489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 3, 3].length) (baseStart_784489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_784489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_784489 prefixEnd_784489 := by exact prefixLift 784489
  have htrace : WordTrace (prefixWord ++ tailWord_784489) baseStart_784489 baseEnd_784489 := by
    simpa [prefixWord, tailWord_784489, baseEnd_784489] using wordTrace_append hprefix tailTrace_784489
  have hstable : (prefixWord ++ tailWord_784489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784489).length < 2 ^ (prefixWord ++ tailWord_784489).sum := by decide
  have hdescent : baseEnd_784489 < baseStart_784489 := by decide
  rcases family_descends (prefixWord ++ tailWord_784489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784503 : List Nat := [1, 1, 3, 1, 1, 5, 3, 2, 4]
def baseStart_784503 : Nat := 118140960795 + 784503 * 2 ^ 59
def prefixEnd_784503 : Nat := 4983230072969 + 3 ^ 40 * 784503 * 2
def baseEnd_784503 : Nat := 179034272841888605379841

theorem tailTrace_784503 : CollatzResearch.WordTrace tailWord_784503 prefixEnd_784503 179034272841888605379841 := by
  unfold tailWord_784503
  simp only [CollatzResearch.WordTrace]
  refine ⟨28613175076887088290622163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19075450051258058860414775 28613175076887088290622163)
  ·
    refine ⟨42919762615330632435933245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28613175076887088290622163 42919762615330632435933245)
    ·
      refine ⟨16094910980748987163474967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42919762615330632435933245 16094910980748987163474967)
      ·
        refine ⟨24142366471123480745212451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16094910980748987163474967 24142366471123480745212451)
        ·
          refine ⟨36213549706685221117818677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24142366471123480745212451 36213549706685221117818677)
          ·
            refine ⟨3395020285001739479795501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36213549706685221117818677 3395020285001739479795501)
            ·
              refine ⟨1273132606875652304923313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3395020285001739479795501 1273132606875652304923313)
              ·
                refine ⟨954849455156739228692485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1273132606875652304923313 954849455156739228692485)
                ·
                  refine ⟨179034272841888605379841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 954849455156739228692485 179034272841888605379841)
                  ·
                    rfl

theorem cell21_784503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 4].length) (baseStart_784503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_784503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_784503 prefixEnd_784503 := by exact prefixLift 784503
  have htrace : WordTrace (prefixWord ++ tailWord_784503) baseStart_784503 baseEnd_784503 := by
    simpa [prefixWord, tailWord_784503, baseEnd_784503] using wordTrace_append hprefix tailTrace_784503
  have hstable : (prefixWord ++ tailWord_784503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784503).length < 2 ^ (prefixWord ++ tailWord_784503).sum := by decide
  have hdescent : baseEnd_784503 < baseStart_784503 := by decide
  rcases family_descends (prefixWord ++ tailWord_784503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784551 : List Nat := [1, 1, 6, 2, 3, 1, 7]
def baseStart_784551 : Nat := 118140960795 + 784551 * 2 ^ 59
def prefixEnd_784551 : Nat := 4983230072969 + 3 ^ 40 * 784551 * 2
def baseEnd_784551 : Nat := 19893914121761243175527

theorem tailTrace_784551 : CollatzResearch.WordTrace tailWord_784551 prefixEnd_784551 19893914121761243175527 := by
  unfold tailWord_784551
  simp only [CollatzResearch.WordTrace]
  refine ⟨28614925780713192488369507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19076617187142128325579671 28614925780713192488369507)
  ·
    refine ⟨42922388671069788732554261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28614925780713192488369507 42922388671069788732554261)
    ·
      refine ⟨2011986968956396346838481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42922388671069788732554261 2011986968956396346838481)
      ·
        refine ⟨1508990226717297260128861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2011986968956396346838481 1508990226717297260128861)
        ·
          refine ⟨565871335018986472548323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1508990226717297260128861 565871335018986472548323)
          ·
            refine ⟨848807002528479708822485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565871335018986472548323 848807002528479708822485)
            ·
              refine ⟨19893914121761243175527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 848807002528479708822485 19893914121761243175527)
              ·
                rfl

theorem cell21_784551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 7].length) (baseStart_784551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_784551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_784551 prefixEnd_784551 := by exact prefixLift 784551
  have htrace : WordTrace (prefixWord ++ tailWord_784551) baseStart_784551 baseEnd_784551 := by
    simpa [prefixWord, tailWord_784551, baseEnd_784551] using wordTrace_append hprefix tailTrace_784551
  have hstable : (prefixWord ++ tailWord_784551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784551).length < 2 ^ (prefixWord ++ tailWord_784551).sum := by decide
  have hdescent : baseEnd_784551 < baseStart_784551 := by decide
  rcases family_descends (prefixWord ++ tailWord_784551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784562 : List Nat := [3, 2, 1, 1, 1, 3, 1, 3, 6]
def baseStart_784562 : Nat := 118140960795 + 784562 * 2 ^ 59
def prefixEnd_784562 : Nat := 4983230072969 + 3 ^ 40 * 784562 * 2
def baseEnd_784562 : Nat := 179047737445717613896387

theorem tailTrace_784562 : CollatzResearch.WordTrace tailWord_784562 prefixEnd_784562 179047737445717613896387 := by
  unfold tailWord_784562
  simp only [CollatzResearch.WordTrace]
  refine ⟨7153831745918335341754985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19076884655782227578013293 7153831745918335341754985)
  ·
    refine ⟨5365373809438751506316239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7153831745918335341754985 5365373809438751506316239)
    ·
      refine ⟨8048060714158127259474359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5365373809438751506316239 8048060714158127259474359)
      ·
        refine ⟨12072091071237190889211539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8048060714158127259474359 12072091071237190889211539)
        ·
          refine ⟨18108136606855786333817309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12072091071237190889211539 18108136606855786333817309)
          ·
            refine ⟨6790551227570919875181491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18108136606855786333817309 6790551227570919875181491)
            ·
              refine ⟨10185826841356379812772237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6790551227570919875181491 10185826841356379812772237)
              ·
                refine ⟨3819685065508642429789589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10185826841356379812772237 3819685065508642429789589)
                ·
                  refine ⟨179047737445717613896387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3819685065508642429789589 179047737445717613896387)
                  ·
                    rfl

theorem cell21_784562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_784562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_784562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_784562 prefixEnd_784562 := by exact prefixLift 784562
  have htrace : WordTrace (prefixWord ++ tailWord_784562) baseStart_784562 baseEnd_784562 := by
    simpa [prefixWord, tailWord_784562, baseEnd_784562] using wordTrace_append hprefix tailTrace_784562
  have hstable : (prefixWord ++ tailWord_784562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784562).length < 2 ^ (prefixWord ++ tailWord_784562).sum := by decide
  have hdescent : baseEnd_784562 < baseStart_784562 := by decide
  rcases family_descends (prefixWord ++ tailWord_784562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784672 : List Nat := [2, 1, 1, 5, 2, 3, 1, 2, 4]
def baseStart_784672 : Nat := 118140960795 + 784672 * 2 ^ 59
def prefixEnd_784672 : Nat := 4983230072969 + 3 ^ 40 * 784672 * 2
def baseEnd_784672 : Nat := 179072840944381867062829

theorem tailTrace_784672 : CollatzResearch.WordTrace tailWord_784672 prefixEnd_784672 179072840944381867062829 := by
  unfold tailWord_784672
  simp only [CollatzResearch.WordTrace]
  refine ⟨14309669506637415076762135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19079559342183220102349513 14309669506637415076762135)
  ·
    refine ⟨21464504259956122615143203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14309669506637415076762135 21464504259956122615143203)
    ·
      refine ⟨32196756389934183922714805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21464504259956122615143203 32196756389934183922714805)
      ·
        refine ⟨3018445911556329742754513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32196756389934183922714805 3018445911556329742754513)
        ·
          refine ⟨2263834433667247307065885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3018445911556329742754513 2263834433667247307065885)
          ·
            refine ⟨848937912625217740149707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2263834433667247307065885 848937912625217740149707)
            ·
              refine ⟨1273406868937826610224561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 848937912625217740149707 1273406868937826610224561)
              ·
                refine ⟨955055151703369957668421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1273406868937826610224561 955055151703369957668421)
                ·
                  refine ⟨179072840944381867062829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 955055151703369957668421 179072840944381867062829)
                  ·
                    rfl

theorem cell21_784672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 4].length) (baseStart_784672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_784672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_784672 prefixEnd_784672 := by exact prefixLift 784672
  have htrace : WordTrace (prefixWord ++ tailWord_784672) baseStart_784672 baseEnd_784672 := by
    simpa [prefixWord, tailWord_784672, baseEnd_784672] using wordTrace_append hprefix tailTrace_784672
  have hstable : (prefixWord ++ tailWord_784672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784672).length < 2 ^ (prefixWord ++ tailWord_784672).sum := by decide
  have hdescent : baseEnd_784672 < baseStart_784672 := by decide
  rcases family_descends (prefixWord ++ tailWord_784672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
