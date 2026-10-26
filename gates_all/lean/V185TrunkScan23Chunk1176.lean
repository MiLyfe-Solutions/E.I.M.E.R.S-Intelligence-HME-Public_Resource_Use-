import V185TrunkScan23Chunk1175

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6966972 : List Nat := [2, 2, 2, 3, 1, 3, 1, 2, 2, 1, 4]
def baseStart_6966972 : Nat := 118140960795 + 6966972 * 2 ^ 59
def prefixEnd_6966972 : Nat := 4983230072969 + 3 ^ 40 * 6966972 * 2
def baseEnd_6966972 : Nat := 3577405342416020923709485

theorem tailTrace_6966972 : CollatzResearch.WordTrace tailWord_6966972 prefixEnd_6966972 3577405342416020923709485 := by
  unfold tailWord_6966972
  simp only [CollatzResearch.WordTrace]
  refine ⟨127053172257928891466395585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169404229677238521955194113 127053172257928891466395585)
  ·
    refine ⟨95289879193446668599796689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127053172257928891466395585 95289879193446668599796689)
    ·
      refine ⟨71467409395085001449847517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95289879193446668599796689 71467409395085001449847517)
      ·
        refine ⟨26800278523156875543692819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71467409395085001449847517 26800278523156875543692819)
        ·
          refine ⟨40200417784735313315539229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26800278523156875543692819 40200417784735313315539229)
          ·
            refine ⟨15075156669275742493327211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40200417784735313315539229 15075156669275742493327211)
            ·
              refine ⟨22612735003913613739990817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15075156669275742493327211 22612735003913613739990817)
              ·
                refine ⟨16959551252935210304993113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22612735003913613739990817 16959551252935210304993113)
                ·
                  refine ⟨12719663439701407728744835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16959551252935210304993113 12719663439701407728744835)
                  ·
                    refine ⟨19079495159552111593117253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12719663439701407728744835 19079495159552111593117253)
                    ·
                      refine ⟨3577405342416020923709485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19079495159552111593117253 3577405342416020923709485)
                      ·
                        rfl

theorem cell23_6966972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_6966972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966972 prefixEnd_6966972 := by exact prefixLift 6966972
  have htrace : WordTrace (prefixWord ++ tailWord_6966972) baseStart_6966972 baseEnd_6966972 := by
    simpa [prefixWord, tailWord_6966972, baseEnd_6966972] using wordTrace_append hprefix tailTrace_6966972
  have hstable : (prefixWord ++ tailWord_6966972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966972).length < 2 ^ (prefixWord ++ tailWord_6966972).sum := by decide
  have hdescent : baseEnd_6966972 < baseStart_6966972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967009 : List Nat := [1, 2, 3, 1, 5, 1, 2, 1, 2, 2, 3]
def baseStart_6967009 : Nat := 118140960795 + 6967009 * 2 ^ 59
def prefixEnd_6967009 : Nat := 4983230072969 + 3 ^ 40 * 6967009 * 2
def baseEnd_6967009 : Nat := 3577424341200237278946815

theorem tailTrace_6967009 : CollatzResearch.WordTrace tailWord_6967009 prefixEnd_6967009 3577424341200237278946815 := by
  unfold tailWord_6967009
  simp only [CollatzResearch.WordTrace]
  refine ⟨254107694016723738251888081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169405129344482492167925387 254107694016723738251888081)
  ·
    refine ⟨190580770512542803688916061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254107694016723738251888081 190580770512542803688916061)
    ·
      refine ⟨71467788942203551383343523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190580770512542803688916061 71467788942203551383343523)
      ·
        refine ⟨107201683413305327075015285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71467788942203551383343523 107201683413305327075015285)
        ·
          refine ⟨10050157819997374413282683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107201683413305327075015285 10050157819997374413282683)
          ·
            refine ⟨15075236729996061619924025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10050157819997374413282683 15075236729996061619924025)
            ·
              refine ⟨11306427547497046214943019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15075236729996061619924025 11306427547497046214943019)
              ·
                refine ⟨16959641321245569322414529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11306427547497046214943019 16959641321245569322414529)
                ·
                  refine ⟨12719730990934176991810897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16959641321245569322414529 12719730990934176991810897)
                  ·
                    refine ⟨9539798243200632743858173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12719730990934176991810897 9539798243200632743858173)
                    ·
                      refine ⟨3577424341200237278946815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9539798243200632743858173 3577424341200237278946815)
                      ·
                        rfl

theorem cell23_6967009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_6967009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967009 prefixEnd_6967009 := by exact prefixLift 6967009
  have htrace : WordTrace (prefixWord ++ tailWord_6967009) baseStart_6967009 baseEnd_6967009 := by
    simpa [prefixWord, tailWord_6967009, baseEnd_6967009] using wordTrace_append hprefix tailTrace_6967009
  have hstable : (prefixWord ++ tailWord_6967009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967009).length < 2 ^ (prefixWord ++ tailWord_6967009).sum := by decide
  have hdescent : baseEnd_6967009 < baseStart_6967009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967032 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 4, 3, 2]
def baseStart_6967032 : Nat := 118140960795 + 6967032 * 2 ^ 59
def prefixEnd_6967032 : Nat := 4983230072969 + 3 ^ 40 * 6967032 * 2
def baseEnd_6967032 : Nat := 3577436151255290688959209

theorem tailTrace_6967032 : CollatzResearch.WordTrace tailWord_6967032 prefixEnd_6967032 3577436151255290688959209 := by
  unfold tailWord_6967032
  simp only [CollatzResearch.WordTrace]
  refine ⟨127054266447820206589987675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169405688597093608786650233 127054266447820206589987675)
  ·
    refine ⟨190581399671730309884981513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127054266447820206589987675 190581399671730309884981513)
    ·
      refine ⟨142936049753797732413736135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190581399671730309884981513 142936049753797732413736135)
      ·
        refine ⟨214404074630696598620604203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142936049753797732413736135 214404074630696598620604203)
        ·
          refine ⟨321606111946044897930906305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214404074630696598620604203 321606111946044897930906305)
          ·
            refine ⟨241204583959533673448179729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321606111946044897930906305 241204583959533673448179729)
            ·
              refine ⟨180903437969650255086134797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241204583959533673448179729 180903437969650255086134797)
              ·
                refine ⟨67838789238618845657300549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180903437969650255086134797 67838789238618845657300549)
                ·
                  refine ⟨12719772982241033560743853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67838789238618845657300549 12719772982241033560743853)
                  ·
                    refine ⟨4769914868340387585278945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12719772982241033560743853 4769914868340387585278945)
                    ·
                      refine ⟨3577436151255290688959209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4769914868340387585278945 3577436151255290688959209)
                      ·
                        rfl

theorem cell23_6967032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 4, 3, 2].length) (baseStart_6967032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967032 prefixEnd_6967032 := by exact prefixLift 6967032
  have htrace : WordTrace (prefixWord ++ tailWord_6967032) baseStart_6967032 baseEnd_6967032 := by
    simpa [prefixWord, tailWord_6967032, baseEnd_6967032] using wordTrace_append hprefix tailTrace_6967032
  have hstable : (prefixWord ++ tailWord_6967032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967032).length < 2 ^ (prefixWord ++ tailWord_6967032).sum := by decide
  have hdescent : baseEnd_6967032 < baseStart_6967032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967042 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 5, 5]
def baseStart_6967042 : Nat := 118140960795 + 6967042 * 2 ^ 59
def prefixEnd_6967042 : Nat := 4983230072969 + 3 ^ 40 * 6967042 * 2
def baseEnd_6967042 : Nat := 1192480428687278549944721

theorem tailTrace_6967042 : CollatzResearch.WordTrace tailWord_6967042 prefixEnd_6967042 1192480428687278549944721 := by
  unfold tailWord_6967042
  simp only [CollatzResearch.WordTrace]
  refine ⟨63527224406401046221959845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169405931750402789925226253 63527224406401046221959845)
  ·
    refine ⟨11911354576200196166617471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63527224406401046221959845 11911354576200196166617471)
    ·
      refine ⟨17867031864300294249926207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11911354576200196166617471 17867031864300294249926207)
      ·
        refine ⟨26800547796450441374889311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17867031864300294249926207 26800547796450441374889311)
        ·
          refine ⟨40200821694675662062333967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26800547796450441374889311 40200821694675662062333967)
          ·
            refine ⟨60301232542013493093500951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40200821694675662062333967 60301232542013493093500951)
            ·
              refine ⟨90451848813020239640251427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60301232542013493093500951 90451848813020239640251427)
              ·
                refine ⟨135677773219530359460377141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90451848813020239640251427 135677773219530359460377141)
                ·
                  refine ⟨12719791239330971199410357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135677773219530359460377141 12719791239330971199410357)
                  ·
                    refine ⟨1192480428687278549944721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12719791239330971199410357 1192480428687278549944721)
                    ·
                      rfl

theorem cell23_6967042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_6967042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967042 prefixEnd_6967042 := by exact prefixLift 6967042
  have htrace : WordTrace (prefixWord ++ tailWord_6967042) baseStart_6967042 baseEnd_6967042 := by
    simpa [prefixWord, tailWord_6967042, baseEnd_6967042] using wordTrace_append hprefix tailTrace_6967042
  have hstable : (prefixWord ++ tailWord_6967042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967042).length < 2 ^ (prefixWord ++ tailWord_6967042).sum := by decide
  have hdescent : baseEnd_6967042 < baseStart_6967042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967060 : List Nat := [2, 4, 4, 1, 1, 2, 1, 1, 2, 2, 3]
def baseStart_6967060 : Nat := 118140960795 + 6967060 * 2 ^ 59
def prefixEnd_6967060 : Nat := 4983230072969 + 3 ^ 40 * 6967060 * 2
def baseEnd_6967060 : Nat := 3577450528713616579409081

theorem tailTrace_6967060 : CollatzResearch.WordTrace tailWord_6967060 prefixEnd_6967060 3577450528713616579409081 := by
  unfold tailWord_6967060
  simp only [CollatzResearch.WordTrace]
  refine ⟨127054777069769486980997317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169406369426359315974663089 127054777069769486980997317)
  ·
    refine ⟨23822770700581778808936997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127054777069769486980997317 23822770700581778808936997)
    ·
      refine ⟨4466769506359083526675687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23822770700581778808936997 4466769506359083526675687)
      ·
        refine ⟨6700154259538625290013531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4466769506359083526675687 6700154259538625290013531)
        ·
          refine ⟨10050231389307937935020297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6700154259538625290013531 10050231389307937935020297)
          ·
            refine ⟨7537673541980953451265223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10050231389307937935020297 7537673541980953451265223)
            ·
              refine ⟨11306510312971430176897835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7537673541980953451265223 11306510312971430176897835)
              ·
                refine ⟨16959765469457145265346753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11306510312971430176897835 16959765469457145265346753)
                ·
                  refine ⟨12719824102092858949010065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16959765469457145265346753 12719824102092858949010065)
                  ·
                    refine ⟨9539868076569644211757549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12719824102092858949010065 9539868076569644211757549)
                    ·
                      refine ⟨3577450528713616579409081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9539868076569644211757549 3577450528713616579409081)
                      ·
                        rfl

theorem cell23_6967060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_6967060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967060 prefixEnd_6967060 := by exact prefixLift 6967060
  have htrace : WordTrace (prefixWord ++ tailWord_6967060) baseStart_6967060 baseEnd_6967060 := by
    simpa [prefixWord, tailWord_6967060, baseEnd_6967060] using wordTrace_append hprefix tailTrace_6967060
  have hstable : (prefixWord ++ tailWord_6967060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967060).length < 2 ^ (prefixWord ++ tailWord_6967060).sum := by decide
  have hdescent : baseEnd_6967060 < baseStart_6967060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967066 : List Nat := [3, 1, 1, 3, 2, 4, 1, 1, 2, 3, 2]
def baseStart_6967066 : Nat := 118140960795 + 6967066 * 2 ^ 59
def prefixEnd_6967066 : Nat := 4983230072969 + 3 ^ 40 * 6967066 * 2
def baseEnd_6967066 : Nat := 3577453609597543555934053

theorem tailTrace_6967066 : CollatzResearch.WordTrace tailWord_6967066 prefixEnd_6967066 3577453609597543555934053 := by
  unfold tailWord_6967066
  simp only [CollatzResearch.WordTrace]
  refine ⟨63527443244379309246678263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169406515318344824657808701 63527443244379309246678263)
  ·
    refine ⟨95291164866568963870017395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63527443244379309246678263 95291164866568963870017395)
    ·
      refine ⟨142936747299853445805026093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95291164866568963870017395 142936747299853445805026093)
      ·
        refine ⟨53601280237445042176884785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142936747299853445805026093 53601280237445042176884785)
        ·
          refine ⟨40200960178083781632663589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53601280237445042176884785 40200960178083781632663589)
          ·
            refine ⟨7537680033390709056124423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40200960178083781632663589 7537680033390709056124423)
            ·
              refine ⟨11306520050086063584186635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7537680033390709056124423 11306520050086063584186635)
              ·
                refine ⟨16959780075129095376279953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11306520050086063584186635 16959780075129095376279953)
                ·
                  refine ⟨12719835056346821532209965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16959780075129095376279953 12719835056346821532209965)
                  ·
                    refine ⟨4769938146130058074578737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12719835056346821532209965 4769938146130058074578737)
                    ·
                      refine ⟨3577453609597543555934053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4769938146130058074578737 3577453609597543555934053)
                      ·
                        rfl

theorem cell23_6967066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_6967066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967066 prefixEnd_6967066 := by exact prefixLift 6967066
  have htrace : WordTrace (prefixWord ++ tailWord_6967066) baseStart_6967066 baseEnd_6967066 := by
    simpa [prefixWord, tailWord_6967066, baseEnd_6967066] using wordTrace_append hprefix tailTrace_6967066
  have hstable : (prefixWord ++ tailWord_6967066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967066).length < 2 ^ (prefixWord ++ tailWord_6967066).sum := by decide
  have hdescent : baseEnd_6967066 < baseStart_6967066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967072 : List Nat := [2, 1, 1, 5, 1, 1, 2, 2, 4, 4]
def baseStart_6967072 : Nat := 118140960795 + 6967072 * 2 ^ 59
def prefixEnd_6967072 : Nat := 4983230072969 + 3 ^ 40 * 6967072 * 2
def baseEnd_6967072 : Nat := 1192485563493823510819675

theorem tailTrace_6967072 : CollatzResearch.WordTrace tailWord_6967072 prefixEnd_6967072 1192485563493823510819675 := by
  unfold tailWord_6967072
  simp only [CollatzResearch.WordTrace]
  refine ⟨127054995907747750005715735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169406661210330333340954313 127054995907747750005715735)
  ·
    refine ⟨190582493861621625008573603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127054995907747750005715735 190582493861621625008573603)
    ·
      refine ⟨285873740792432437512860405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190582493861621625008573603 285873740792432437512860405)
      ·
        refine ⟨26800663199290541016830663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 285873740792432437512860405 26800663199290541016830663)
        ·
          refine ⟨40200994798935811525245995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26800663199290541016830663 40200994798935811525245995)
          ·
            refine ⟨60301492198403717287868993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40200994798935811525245995 60301492198403717287868993)
            ·
              refine ⟨45226119148802787965901745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60301492198403717287868993 45226119148802787965901745)
              ·
                refine ⟨33919589361602090974426309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45226119148802787965901745 33919589361602090974426309)
                ·
                  refine ⟨6359923005300392057704933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33919589361602090974426309 6359923005300392057704933)
                  ·
                    refine ⟨1192485563493823510819675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6359923005300392057704933 1192485563493823510819675)
                    ·
                      rfl

theorem cell23_6967072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 4, 4].length) (baseStart_6967072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967072 prefixEnd_6967072 := by exact prefixLift 6967072
  have htrace : WordTrace (prefixWord ++ tailWord_6967072) baseStart_6967072 baseEnd_6967072 := by
    simpa [prefixWord, tailWord_6967072, baseEnd_6967072] using wordTrace_append hprefix tailTrace_6967072
  have hstable : (prefixWord ++ tailWord_6967072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967072).length < 2 ^ (prefixWord ++ tailWord_6967072).sum := by decide
  have hdescent : baseEnd_6967072 < baseStart_6967072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967076 : List Nat := [2, 3, 1, 3, 2, 3, 2, 1, 1, 5]
def baseStart_6967076 : Nat := 118140960795 + 6967076 * 2 ^ 59
def prefixEnd_6967076 : Nat := 4983230072969 + 3 ^ 40 * 6967076 * 2
def baseEnd_6967076 : Nat := 1192486248134696172269669

theorem tailTrace_6967076 : CollatzResearch.WordTrace tailWord_6967076 prefixEnd_6967076 1192486248134696172269669 := by
  unfold tailWord_6967076
  simp only [CollatzResearch.WordTrace]
  refine ⟨127055068853740504347288541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169406758471654005796384721 127055068853740504347288541)
  ·
    refine ⟨47645650820152689130233203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127055068853740504347288541 47645650820152689130233203)
    ·
      refine ⟨71468476230229033695349805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47645650820152689130233203 71468476230229033695349805)
      ·
        refine ⟨26800678586335887635756177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71468476230229033695349805 26800678586335887635756177)
        ·
          refine ⟨20100508939751915726817133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26800678586335887635756177 20100508939751915726817133)
          ·
            refine ⟨7537690852406968397556425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20100508939751915726817133 7537690852406968397556425)
            ·
              refine ⟨5653268139305226298167319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7537690852406968397556425 5653268139305226298167319)
              ·
                refine ⟨8479902208957839447250979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5653268139305226298167319 8479902208957839447250979)
                ·
                  refine ⟨12719853313436759170876469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8479902208957839447250979 12719853313436759170876469)
                  ·
                    refine ⟨1192486248134696172269669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12719853313436759170876469 1192486248134696172269669)
                    ·
                      rfl

theorem cell23_6967076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_6967076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967076 prefixEnd_6967076 := by exact prefixLift 6967076
  have htrace : WordTrace (prefixWord ++ tailWord_6967076) baseStart_6967076 baseEnd_6967076 := by
    simpa [prefixWord, tailWord_6967076, baseEnd_6967076] using wordTrace_append hprefix tailTrace_6967076
  have hstable : (prefixWord ++ tailWord_6967076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967076).length < 2 ^ (prefixWord ++ tailWord_6967076).sum := by decide
  have hdescent : baseEnd_6967076 < baseStart_6967076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967089 : List Nat := [1, 2, 2, 3, 2, 2, 3, 2, 2, 4]
def baseStart_6967089 : Nat := 118140960795 + 6967089 * 2 ^ 59
def prefixEnd_6967089 : Nat := 4983230072969 + 3 ^ 40 * 6967089 * 2
def baseEnd_6967089 : Nat := 1192488473217532321982149

theorem tailTrace_6967089 : CollatzResearch.WordTrace tailWord_6967089 prefixEnd_6967089 1192488473217532321982149 := by
  unfold tailWord_6967089
  simp only [CollatzResearch.WordTrace]
  refine ⟨254110611856433911914800321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169407074570955941276533547 254110611856433911914800321)
  ·
    refine ⟨190582958892325433936100241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254110611856433911914800321 190582958892325433936100241)
    ·
      refine ⟨142937219169244075452075181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190582958892325433936100241 142937219169244075452075181)
      ·
        refine ⟨53601457188466528294528193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142937219169244075452075181 53601457188466528294528193)
        ·
          refine ⟨40201092891349896220896145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53601457188466528294528193 40201092891349896220896145)
          ·
            refine ⟨30150819668512422165672109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40201092891349896220896145 30150819668512422165672109)
            ·
              refine ⟨11306557375692158312127041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30150819668512422165672109 11306557375692158312127041)
              ·
                refine ⟨8479918031769118734095281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11306557375692158312127041 8479918031769118734095281)
                ·
                  refine ⟨6359938523826839050571461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8479918031769118734095281 6359938523826839050571461)
                  ·
                    refine ⟨1192488473217532321982149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6359938523826839050571461 1192488473217532321982149)
                    ·
                      rfl

theorem cell23_6967089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 2, 4].length) (baseStart_6967089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967089 prefixEnd_6967089 := by exact prefixLift 6967089
  have htrace : WordTrace (prefixWord ++ tailWord_6967089) baseStart_6967089 baseEnd_6967089 := by
    simpa [prefixWord, tailWord_6967089, baseEnd_6967089] using wordTrace_append hprefix tailTrace_6967089
  have hstable : (prefixWord ++ tailWord_6967089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967089).length < 2 ^ (prefixWord ++ tailWord_6967089).sum := by decide
  have hdescent : baseEnd_6967089 < baseStart_6967089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967096 : List Nat := [2, 1, 2, 1, 3, 4, 2, 1, 3, 2, 2]
def baseStart_6967096 : Nat := 118140960795 + 6967096 * 2 ^ 59
def prefixEnd_6967096 : Nat := 4983230072969 + 3 ^ 40 * 6967096 * 2
def baseEnd_6967096 : Nat := 3577469014017178438558915

theorem tailTrace_6967096 : CollatzResearch.WordTrace tailWord_6967096 prefixEnd_6967096 3577469014017178438558915 := by
  unfold tailWord_6967096
  simp only [CollatzResearch.WordTrace]
  refine ⟨127055433583704276055152571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169407244778272368073536761 127055433583704276055152571)
  ·
    refine ⟨190583150375556414082728857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127055433583704276055152571 190583150375556414082728857)
    ·
      refine ⟨142937362781667310562046643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190583150375556414082728857 142937362781667310562046643)
      ·
        refine ⟨214406044172500965843069965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142937362781667310562046643 214406044172500965843069965)
        ·
          refine ⟨80402266564687862191151237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214406044172500965843069965 80402266564687862191151237)
          ·
            refine ⟨15075424980878974160840857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80402266564687862191151237 15075424980878974160840857)
            ·
              refine ⟨11306568735659230620630643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15075424980878974160840857 11306568735659230620630643)
              ·
                refine ⟨16959853103488845930945965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11306568735659230620630643 16959853103488845930945965)
                ·
                  refine ⟨6359944913808317224104737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16959853103488845930945965 6359944913808317224104737)
                  ·
                    refine ⟨4769958685356237918078553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6359944913808317224104737 4769958685356237918078553)
                    ·
                      refine ⟨3577469014017178438558915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4769958685356237918078553 3577469014017178438558915)
                      ·
                        rfl

theorem cell23_6967096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 3, 2, 2].length) (baseStart_6967096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967096 prefixEnd_6967096 := by exact prefixLift 6967096
  have htrace : WordTrace (prefixWord ++ tailWord_6967096) baseStart_6967096 baseEnd_6967096 := by
    simpa [prefixWord, tailWord_6967096, baseEnd_6967096] using wordTrace_append hprefix tailTrace_6967096
  have hstable : (prefixWord ++ tailWord_6967096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967096).length < 2 ^ (prefixWord ++ tailWord_6967096).sum := by decide
  have hdescent : baseEnd_6967096 < baseStart_6967096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967116 : List Nat := [2, 2, 1, 3, 4, 1, 2, 2, 1, 2, 3]
def baseStart_6967116 : Nat := 118140960795 + 6967116 * 2 ^ 59
def prefixEnd_6967116 : Nat := 4983230072969 + 3 ^ 40 * 6967116 * 2
def baseEnd_6967116 : Nat := 3577479283630268360308823

theorem tailTrace_6967116 : CollatzResearch.WordTrace tailWord_6967116 prefixEnd_6967116 3577479283630268360308823 := by
  unfold tailWord_6967116
  simp only [CollatzResearch.WordTrace]
  refine ⟨127055798313668047763016601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169407731084890730350688801 127055798313668047763016601)
  ·
    refine ⟨95291848735251035822262451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127055798313668047763016601 95291848735251035822262451)
    ·
      refine ⟨142937773102876553733393677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95291848735251035822262451 142937773102876553733393677)
      ·
        refine ⟨53601664913578707650022629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142937773102876553733393677 53601664913578707650022629)
        ·
          refine ⟨10050312171296007684379243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53601664913578707650022629 10050312171296007684379243)
          ·
            refine ⟨15075468256944011526568865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10050312171296007684379243 15075468256944011526568865)
            ·
              refine ⟨11306601192708008644926649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15075468256944011526568865 11306601192708008644926649)
              ·
                refine ⟨8479950894531006483694987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11306601192708008644926649 8479950894531006483694987)
                ·
                  refine ⟨12719926341796509725542481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8479950894531006483694987 12719926341796509725542481)
                  ·
                    refine ⟨9539944756347382294156861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12719926341796509725542481 9539944756347382294156861)
                    ·
                      refine ⟨3577479283630268360308823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9539944756347382294156861 3577479283630268360308823)
                      ·
                        rfl

theorem cell23_6967116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_6967116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967116 prefixEnd_6967116 := by exact prefixLift 6967116
  have htrace : WordTrace (prefixWord ++ tailWord_6967116) baseStart_6967116 baseEnd_6967116 := by
    simpa [prefixWord, tailWord_6967116, baseEnd_6967116] using wordTrace_append hprefix tailTrace_6967116
  have hstable : (prefixWord ++ tailWord_6967116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967116).length < 2 ^ (prefixWord ++ tailWord_6967116).sum := by decide
  have hdescent : baseEnd_6967116 < baseStart_6967116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967145 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 4, 6]
def baseStart_6967145 : Nat := 118140960795 + 6967145 * 2 ^ 59
def prefixEnd_6967145 : Nat := 4983230072969 + 3 ^ 40 * 6967145 * 2
def baseEnd_6967145 : Nat := 1192498058189749582282063

theorem tailTrace_6967145 : CollatzResearch.WordTrace tailWord_6967145 prefixEnd_6967145 1192498058189749582282063 := by
  unfold tailWord_6967145
  simp only [CollatzResearch.WordTrace]
  refine ⟨254112654344231033478838889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169408436229487355652559259 254112654344231033478838889)
  ·
    refine ⟨190584490758173275109129167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254112654344231033478838889 190584490758173275109129167)
    ·
      refine ⟨285876736137259912663693751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190584490758173275109129167 285876736137259912663693751)
      ·
        refine ⟨428815104205889868995540627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285876736137259912663693751 428815104205889868995540627)
        ·
          refine ⟨643222656308834803493310941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428815104205889868995540627 643222656308834803493310941)
          ·
            refine ⟨241208496115813051309991603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 643222656308834803493310941 241208496115813051309991603)
            ·
              refine ⟨361812744173719576964987405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241208496115813051309991603 361812744173719576964987405)
              ·
                refine ⟨135679779065144841361870277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 361812744173719576964987405 135679779065144841361870277)
                ·
                  refine ⟨25439958574714657755350677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135679779065144841361870277 25439958574714657755350677)
                  ·
                    refine ⟨1192498058189749582282063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25439958574714657755350677 1192498058189749582282063)
                    ·
                      rfl

theorem cell23_6967145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 6].length) (baseStart_6967145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967145 prefixEnd_6967145 := by exact prefixLift 6967145
  have htrace : WordTrace (prefixWord ++ tailWord_6967145) baseStart_6967145 baseEnd_6967145 := by
    simpa [prefixWord, tailWord_6967145, baseEnd_6967145] using wordTrace_append hprefix tailTrace_6967145
  have hstable : (prefixWord ++ tailWord_6967145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967145).length < 2 ^ (prefixWord ++ tailWord_6967145).sum := by decide
  have hdescent : baseEnd_6967145 < baseStart_6967145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967155 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 5]
def baseStart_6967155 : Nat := 118140960795 + 6967155 * 2 ^ 59
def prefixEnd_6967155 : Nat := 4983230072969 + 3 ^ 40 * 6967155 * 2
def baseEnd_6967155 : Nat := 3577499309375793707721143

theorem tailTrace_6967155 : CollatzResearch.WordTrace tailWord_6967155 prefixEnd_6967155 3577499309375793707721143 := by
  unfold tailWord_6967155
  simp only [CollatzResearch.WordTrace]
  refine ⟨254113019074194805186702919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169408679382796536791135279 254113019074194805186702919)
  ·
    refine ⟨381169528611292207780054379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254113019074194805186702919 381169528611292207780054379)
    ·
      refine ⟨571754292916938311670081569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381169528611292207780054379 571754292916938311670081569)
      ·
        refine ⟨428815719687703733752561177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 571754292916938311670081569 428815719687703733752561177)
        ·
          refine ⟨321611789765777800314420883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428815719687703733752561177 321611789765777800314420883)
          ·
            refine ⟨482417684648666700471631325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321611789765777800314420883 482417684648666700471631325)
            ·
              refine ⟨180906631743250012676861747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 482417684648666700471631325 180906631743250012676861747)
              ·
                refine ⟨271359947614875019015292621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180906631743250012676861747 271359947614875019015292621)
                ·
                  refine ⟨101759980355578132130734733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 271359947614875019015292621 101759980355578132130734733)
                  ·
                    refine ⟨38159992633341799549025525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101759980355578132130734733 38159992633341799549025525)
                    ·
                      refine ⟨3577499309375793707721143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38159992633341799549025525 3577499309375793707721143)
                      ·
                        rfl

theorem cell23_6967155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 5].length) (baseStart_6967155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967155 prefixEnd_6967155 := by exact prefixLift 6967155
  have htrace : WordTrace (prefixWord ++ tailWord_6967155) baseStart_6967155 baseEnd_6967155 := by
    simpa [prefixWord, tailWord_6967155, baseEnd_6967155] using wordTrace_append hprefix tailTrace_6967155
  have hstable : (prefixWord ++ tailWord_6967155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967155).length < 2 ^ (prefixWord ++ tailWord_6967155).sum := by decide
  have hdescent : baseEnd_6967155 < baseStart_6967155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967172 : List Nat := [2, 3, 2, 1, 1, 1, 3, 2, 2, 1, 5]
def baseStart_6967172 : Nat := 118140960795 + 6967172 * 2 ^ 59
def prefixEnd_6967172 : Nat := 4983230072969 + 3 ^ 40 * 6967172 * 2
def baseEnd_6967172 : Nat := 3577508038546920141208565

theorem tailTrace_6967172 : CollatzResearch.WordTrace tailWord_6967172 prefixEnd_6967172 3577508038546920141208565 := by
  unfold tailWord_6967172
  simp only [CollatzResearch.WordTrace]
  refine ⟨127056819557566608545035885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169409092743422144726714513 127056819557566608545035885)
  ·
    refine ⟨47646307334087478204388457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127056819557566608545035885 47646307334087478204388457)
    ·
      refine ⟨35734730500565608653291343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47646307334087478204388457 35734730500565608653291343)
      ·
        refine ⟨53602095750848412979937015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35734730500565608653291343 53602095750848412979937015)
        ·
          refine ⟨80403143626272619469905523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53602095750848412979937015 80403143626272619469905523)
          ·
            refine ⟨120604715439408929204858285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80403143626272619469905523 120604715439408929204858285)
            ·
              refine ⟨45226768289778348451821857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120604715439408929204858285 45226768289778348451821857)
              ·
                refine ⟨33920076217333761338866393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45226768289778348451821857 33920076217333761338866393)
                ·
                  refine ⟨25440057163000321004149795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33920076217333761338866393 25440057163000321004149795)
                  ·
                    refine ⟨38160085744500481506224693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25440057163000321004149795 38160085744500481506224693)
                    ·
                      refine ⟨3577508038546920141208565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38160085744500481506224693 3577508038546920141208565)
                      ·
                        rfl

theorem cell23_6967172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_6967172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967172 prefixEnd_6967172 := by exact prefixLift 6967172
  have htrace : WordTrace (prefixWord ++ tailWord_6967172) baseStart_6967172 baseEnd_6967172 := by
    simpa [prefixWord, tailWord_6967172, baseEnd_6967172] using wordTrace_append hprefix tailTrace_6967172
  have hstable : (prefixWord ++ tailWord_6967172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967172).length < 2 ^ (prefixWord ++ tailWord_6967172).sum := by decide
  have hdescent : baseEnd_6967172 < baseStart_6967172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967186 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 3, 4, 2]
def baseStart_6967186 : Nat := 118140960795 + 6967186 * 2 ^ 59
def prefixEnd_6967186 : Nat := 4983230072969 + 3 ^ 40 * 6967186 * 2
def baseEnd_6967186 : Nat := 3577515227276083086433501

theorem tailTrace_6967186 : CollatzResearch.WordTrace tailWord_6967186 prefixEnd_6967186 3577515227276083086433501 := by
  unfold tailWord_6967186
  simp only [CollatzResearch.WordTrace]
  refine ⟨63528537434270624370270353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169409433158054998320720941 63528537434270624370270353)
  ·
    refine ⟨47646403075702968277702765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63528537434270624370270353 47646403075702968277702765)
    ·
      refine ⟨17867401153388613104138537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47646403075702968277702765 17867401153388613104138537)
      ·
        refine ⟨13400550865041459828103903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17867401153388613104138537 13400550865041459828103903)
        ·
          refine ⟨20100826297562189742155855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13400550865041459828103903 20100826297562189742155855)
          ·
            refine ⟨30151239446343284613233783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20100826297562189742155855 30151239446343284613233783)
            ·
              refine ⟨45226859169514926919850675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30151239446343284613233783 45226859169514926919850675)
              ·
                refine ⟨67840288754272390379776013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45226859169514926919850675 67840288754272390379776013)
                ·
                  refine ⟨25440108282852146392416005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67840288754272390379776013 25440108282852146392416005)
                  ·
                    refine ⟨4770020303034777448578001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25440108282852146392416005 4770020303034777448578001)
                    ·
                      refine ⟨3577515227276083086433501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4770020303034777448578001 3577515227276083086433501)
                      ·
                        rfl

theorem cell23_6967186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_6967186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967186 prefixEnd_6967186 := by exact prefixLift 6967186
  have htrace : WordTrace (prefixWord ++ tailWord_6967186) baseStart_6967186 baseEnd_6967186 := by
    simpa [prefixWord, tailWord_6967186, baseEnd_6967186] using wordTrace_append hprefix tailTrace_6967186
  have hstable : (prefixWord ++ tailWord_6967186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967186).length < 2 ^ (prefixWord ++ tailWord_6967186).sum := by decide
  have hdescent : baseEnd_6967186 < baseStart_6967186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967220 : List Nat := [2, 5, 2, 1, 2, 1, 2, 1, 1, 4, 2]
def baseStart_6967220 : Nat := 118140960795 + 6967220 * 2 ^ 59
def prefixEnd_6967220 : Nat := 4983230072969 + 3 ^ 40 * 6967220 * 2
def baseEnd_6967220 : Nat := 3577532685618335953408345

theorem tailTrace_6967220 : CollatzResearch.WordTrace tailWord_6967220 prefixEnd_6967220 3577532685618335953408345 := by
  unfold tailWord_6967220
  simp only [CollatzResearch.WordTrace]
  refine ⟨127057694909479660643909557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169410259879306214191879409 127057694909479660643909557)
  ·
    refine ⟨11911658897763718185366521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127057694909479660643909557 11911658897763718185366521)
    ·
      refine ⟨8933744173322788639024891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11911658897763718185366521 8933744173322788639024891)
      ·
        refine ⟨13400616259984182958537337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8933744173322788639024891 13400616259984182958537337)
        ·
          refine ⟨10050462194988137218903003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13400616259984182958537337 10050462194988137218903003)
          ·
            refine ⟨15075693292482205828354505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10050462194988137218903003 15075693292482205828354505)
            ·
              refine ⟨11306769969361654371265879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15075693292482205828354505 11306769969361654371265879)
              ·
                refine ⟨16960154954042481556898819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11306769969361654371265879 16960154954042481556898819)
                ·
                  refine ⟨25440232431063722335348229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16960154954042481556898819 25440232431063722335348229)
                  ·
                    refine ⟨4770043580824447937877793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25440232431063722335348229 4770043580824447937877793)
                    ·
                      refine ⟨3577532685618335953408345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4770043580824447937877793 3577532685618335953408345)
                      ·
                        rfl

theorem cell23_6967220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_6967220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967220 prefixEnd_6967220 := by exact prefixLift 6967220
  have htrace : WordTrace (prefixWord ++ tailWord_6967220) baseStart_6967220 baseEnd_6967220 := by
    simpa [prefixWord, tailWord_6967220, baseEnd_6967220] using wordTrace_append hprefix tailTrace_6967220
  have hstable : (prefixWord ++ tailWord_6967220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967220).length < 2 ^ (prefixWord ++ tailWord_6967220).sum := by decide
  have hdescent : baseEnd_6967220 < baseStart_6967220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967254 : List Nat := [5, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2]
def baseStart_6967254 : Nat := 118140960795 + 6967254 * 2 ^ 59
def prefixEnd_6967254 : Nat := 4983230072969 + 3 ^ 40 * 6967254 * 2
def baseEnd_6967254 : Nat := 3577550143960588820383189

theorem tailTrace_6967254 : CollatzResearch.WordTrace tailWord_6967254 prefixEnd_6967254 3577550143960588820383189 := by
  unfold tailWord_6967254
  simp only [CollatzResearch.WordTrace]
  refine ⟨15882289368802259068409801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169411086600557430063037877 15882289368802259068409801)
  ·
    refine ⟨11911717026601694301307351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15882289368802259068409801 11911717026601694301307351)
    ·
      refine ⟨17867575539902541451961027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11911717026601694301307351 17867575539902541451961027)
      ·
        refine ⟨26801363309853812177941541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17867575539902541451961027 26801363309853812177941541)
        ·
          refine ⟨5025255620597589783364039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26801363309853812177941541 5025255620597589783364039)
          ·
            refine ⟨7537883430896384675046059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5025255620597589783364039 7537883430896384675046059)
            ·
              refine ⟨11306825146344577012569089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7537883430896384675046059 11306825146344577012569089)
              ·
                refine ⟨8480118859758432759426817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11306825146344577012569089 8480118859758432759426817)
                ·
                  refine ⟨6360089144818824569570113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8480118859758432759426817 6360089144818824569570113)
                  ·
                    refine ⟨4770066858614118427177585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6360089144818824569570113 4770066858614118427177585)
                    ·
                      refine ⟨3577550143960588820383189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4770066858614118427177585 3577550143960588820383189)
                      ·
                        rfl

theorem cell23_6967254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_6967254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967254 prefixEnd_6967254 := by exact prefixLift 6967254
  have htrace : WordTrace (prefixWord ++ tailWord_6967254) baseStart_6967254 baseEnd_6967254 := by
    simpa [prefixWord, tailWord_6967254, baseEnd_6967254] using wordTrace_append hprefix tailTrace_6967254
  have hstable : (prefixWord ++ tailWord_6967254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967254).length < 2 ^ (prefixWord ++ tailWord_6967254).sum := by decide
  have hdescent : baseEnd_6967254 < baseStart_6967254 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967272 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 4, 1, 6]
def baseStart_6967272 : Nat := 118140960795 + 6967272 * 2 ^ 59
def prefixEnd_6967272 : Nat := 4983230072969 + 3 ^ 40 * 6967272 * 2
def baseEnd_6967272 : Nat := 3577559386612369749958105

theorem tailTrace_6967272 : CollatzResearch.WordTrace tailWord_6967272 prefixEnd_6967272 3577559386612369749958105 := by
  unfold tailWord_6967272
  simp only [CollatzResearch.WordTrace]
  refine ⟨127058643207385467084356035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169411524276513956112474713 127058643207385467084356035)
  ·
    refine ⟨190587964811078200626534053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127058643207385467084356035 190587964811078200626534053)
    ·
      refine ⟨35735243402077162617475135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190587964811078200626534053 35735243402077162617475135)
      ·
        refine ⟨53602865103115743926212703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35735243402077162617475135 53602865103115743926212703)
        ·
          refine ⟨80404297654673615889319055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53602865103115743926212703 80404297654673615889319055)
          ·
            refine ⟨120606446482010423833978583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80404297654673615889319055 120606446482010423833978583)
            ·
              refine ⟨180909669723015635750967875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120606446482010423833978583 180909669723015635750967875)
              ·
                refine ⟨271364504584523453626451813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180909669723015635750967875 271364504584523453626451813)
                ·
                  refine ⟨50880844609598147554959715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 271364504584523453626451813 50880844609598147554959715)
                  ·
                    refine ⟨76321266914397221332439573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50880844609598147554959715 76321266914397221332439573)
                    ·
                      refine ⟨3577559386612369749958105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76321266914397221332439573 3577559386612369749958105)
                      ·
                        rfl

theorem cell23_6967272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_6967272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967272 prefixEnd_6967272 := by exact prefixLift 6967272
  have htrace : WordTrace (prefixWord ++ tailWord_6967272) baseStart_6967272 baseEnd_6967272 := by
    simpa [prefixWord, tailWord_6967272, baseEnd_6967272] using wordTrace_append hprefix tailTrace_6967272
  have hstable : (prefixWord ++ tailWord_6967272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967272).length < 2 ^ (prefixWord ++ tailWord_6967272).sum := by decide
  have hdescent : baseEnd_6967272 < baseStart_6967272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967303 : List Nat := [1, 1, 4, 3, 1, 2, 3, 3, 1, 4]
def baseStart_6967303 : Nat := 118140960795 + 6967303 * 2 ^ 59
def prefixEnd_6967303 : Nat := 4983230072969 + 3 ^ 40 * 6967303 * 2
def baseEnd_6967303 : Nat := 1192525101504219709556821

theorem tailTrace_6967303 : CollatzResearch.WordTrace tailWord_6967303 prefixEnd_6967303 1192525101504219709556821 := by
  unfold tailWord_6967303
  simp only [CollatzResearch.WordTrace]
  refine ⟨254118417077658626463090563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169412278051772417642060375 254118417077658626463090563)
  ·
    refine ⟨381177625616487939694635845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254118417077658626463090563 381177625616487939694635845)
    ·
      refine ⟨71470804803091488692744221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 381177625616487939694635845 71470804803091488692744221)
      ·
        refine ⟨26801551801159308259779083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71470804803091488692744221 26801551801159308259779083)
        ·
          refine ⟨40202327701738962389668625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26801551801159308259779083 40202327701738962389668625)
          ·
            refine ⟨30151745776304221792251469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40202327701738962389668625 30151745776304221792251469)
            ·
              refine ⟨11306904666114083172094301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30151745776304221792251469 11306904666114083172094301)
              ·
                refine ⟨4240089249792781189535363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11306904666114083172094301 4240089249792781189535363)
                ·
                  refine ⟨6360133874689171784303045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4240089249792781189535363 6360133874689171784303045)
                  ·
                    refine ⟨1192525101504219709556821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6360133874689171784303045 1192525101504219709556821)
                    ·
                      rfl

theorem cell23_6967303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_6967303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967303 prefixEnd_6967303 := by exact prefixLift 6967303
  have htrace : WordTrace (prefixWord ++ tailWord_6967303) baseStart_6967303 baseEnd_6967303 := by
    simpa [prefixWord, tailWord_6967303, baseEnd_6967303] using wordTrace_append hprefix tailTrace_6967303
  have hstable : (prefixWord ++ tailWord_6967303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967303).length < 2 ^ (prefixWord ++ tailWord_6967303).sum := by decide
  have hdescent : baseEnd_6967303 < baseStart_6967303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967346 : List Nat := [3, 2, 1, 1, 2, 3, 3, 2, 1, 5]
def baseStart_6967346 : Nat := 118140960795 + 6967346 * 2 ^ 59
def prefixEnd_6967346 : Nat := 4983230072969 + 3 ^ 40 * 6967346 * 2
def baseEnd_6967346 : Nat := 1192532461393600820144255

theorem tailTrace_6967346 : CollatzResearch.WordTrace tailWord_6967346 prefixEnd_6967346 1192532461393600820144255 := by
  unfold tailWord_6967346
  simp only [CollatzResearch.WordTrace]
  refine ⟨63529996354125711201726473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169413323611001896537937261 63529996354125711201726473)
  ·
    refine ⟨47647497265594283401294855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63529996354125711201726473 47647497265594283401294855)
    ·
      refine ⟨71471245898391425101942283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47647497265594283401294855 71471245898391425101942283)
      ·
        refine ⟨107206868847587137652913425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71471245898391425101942283 107206868847587137652913425)
        ·
          refine ⟨80405151635690353239685069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107206868847587137652913425 80405151635690353239685069)
          ·
            refine ⟨30151931863383882464881901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80405151635690353239685069 30151931863383882464881901)
            ·
              refine ⟨11306974448768955924330713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30151931863383882464881901 11306974448768955924330713)
              ·
                refine ⟨8480230836576716943248035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11306974448768955924330713 8480230836576716943248035)
                ·
                  refine ⟨12720346254865075414872053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8480230836576716943248035 12720346254865075414872053)
                  ·
                    refine ⟨1192532461393600820144255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12720346254865075414872053 1192532461393600820144255)
                    ·
                      rfl

theorem cell23_6967346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_6967346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967346 prefixEnd_6967346 := by exact prefixLift 6967346
  have htrace : WordTrace (prefixWord ++ tailWord_6967346) baseStart_6967346 baseEnd_6967346 := by
    simpa [prefixWord, tailWord_6967346, baseEnd_6967346] using wordTrace_append hprefix tailTrace_6967346
  have hstable : (prefixWord ++ tailWord_6967346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967346).length < 2 ^ (prefixWord ++ tailWord_6967346).sum := by decide
  have hdescent : baseEnd_6967346 < baseStart_6967346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967359 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 6, 4]
def baseStart_6967359 : Nat := 118140960795 + 6967359 * 2 ^ 59
def prefixEnd_6967359 : Nat := 4983230072969 + 3 ^ 40 * 6967359 * 2
def baseEnd_6967359 : Nat := 1192534686476436969856735

theorem tailTrace_6967359 : CollatzResearch.WordTrace tailWord_6967359 prefixEnd_6967359 1192534686476436969856735 := by
  unfold tailWord_6967359
  simp only [CollatzResearch.WordTrace]
  refine ⟨254120459565455748027129131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169413639710303832018086087 254120459565455748027129131)
  ·
    refine ⟨381180689348183622040693697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254120459565455748027129131 381180689348183622040693697)
    ·
      refine ⟨285885517011137716530520273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381180689348183622040693697 285885517011137716530520273)
      ·
        refine ⟨214414137758353287397890205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285885517011137716530520273 214414137758353287397890205)
        ·
          refine ⟨80405301659382482774208827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214414137758353287397890205 80405301659382482774208827)
          ·
            refine ⟨120607952489073724161313241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80405301659382482774208827 120607952489073724161313241)
            ·
              refine ⟨90455964366805293120984931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120607952489073724161313241 90455964366805293120984931)
              ·
                refine ⟨135683946550207939681477397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90455964366805293120984931 135683946550207939681477397)
                ·
                  refine ⟨6360184994540997172569253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135683946550207939681477397 6360184994540997172569253)
                  ·
                    refine ⟨1192534686476436969856735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6360184994540997172569253 1192534686476436969856735)
                    ·
                      rfl

theorem cell23_6967359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 6, 4].length) (baseStart_6967359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967359 prefixEnd_6967359 := by exact prefixLift 6967359
  have htrace : WordTrace (prefixWord ++ tailWord_6967359) baseStart_6967359 baseEnd_6967359 := by
    simpa [prefixWord, tailWord_6967359, baseEnd_6967359] using wordTrace_append hprefix tailTrace_6967359
  have hstable : (prefixWord ++ tailWord_6967359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967359).length < 2 ^ (prefixWord ++ tailWord_6967359).sum := by decide
  have hdescent : baseEnd_6967359 < baseStart_6967359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967406 : List Nat := [4, 1, 2, 2, 1, 1, 5, 7]
def baseStart_6967406 : Nat := 118140960795 + 6967406 * 2 ^ 59
def prefixEnd_6967406 : Nat := 4983230072969 + 3 ^ 40 * 6967406 * 2
def baseEnd_6967406 : Nat := 132504747889632304654907

theorem tailTrace_6967406 : CollatzResearch.WordTrace tailWord_6967406 prefixEnd_6967406 132504747889632304654907 := by
  unfold tailWord_6967406
  simp only [CollatzResearch.WordTrace]
  refine ⟨31765271724535684381761259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169414782530856983369393381 31765271724535684381761259)
  ·
    refine ⟨47647907586803526572641889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31765271724535684381761259 47647907586803526572641889)
    ·
      refine ⟨35735930690102644929481417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47647907586803526572641889 35735930690102644929481417)
      ·
        refine ⟨26801948017576983697111063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35735930690102644929481417 26801948017576983697111063)
        ·
          refine ⟨40202922026365475545666595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26801948017576983697111063 40202922026365475545666595)
          ·
            refine ⟨60304383039548213318499893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40202922026365475545666595 60304383039548213318499893)
            ·
              refine ⟨5653535909957644998609365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60304383039548213318499893 5653535909957644998609365)
              ·
                refine ⟨132504747889632304654907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5653535909957644998609365 132504747889632304654907)
                ·
                  rfl

theorem cell23_6967406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 7].length) (baseStart_6967406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967406 prefixEnd_6967406 := by exact prefixLift 6967406
  have htrace : WordTrace (prefixWord ++ tailWord_6967406) baseStart_6967406 baseEnd_6967406 := by
    simpa [prefixWord, tailWord_6967406, baseEnd_6967406] using wordTrace_append hprefix tailTrace_6967406
  have hstable : (prefixWord ++ tailWord_6967406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967406).length < 2 ^ (prefixWord ++ tailWord_6967406).sum := by decide
  have hdescent : baseEnd_6967406 < baseStart_6967406 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967416 : List Nat := [2, 1, 2, 1, 1, 1, 3, 4, 4, 1, 3]
def baseStart_6967416 : Nat := 118140960795 + 6967416 * 2 ^ 59
def prefixEnd_6967416 : Nat := 4983230072969 + 3 ^ 40 * 6967416 * 2
def baseEnd_6967416 : Nat := 3577633327826617186557443

theorem tailTrace_6967416 : CollatzResearch.WordTrace tailWord_6967416 prefixEnd_6967416 3577633327826617186557443 := by
  unfold tailWord_6967416
  simp only [CollatzResearch.WordTrace]
  refine ⟨127061269263124623380977051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169415025684166164507969401 127061269263124623380977051)
  ·
    refine ⟨190591903894686935071465577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127061269263124623380977051 190591903894686935071465577)
    ·
      refine ⟨142943927921015201303599183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190591903894686935071465577 142943927921015201303599183)
      ·
        refine ⟨214415891881522801955398775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142943927921015201303599183 214415891881522801955398775)
        ·
          refine ⟨321623837822284202933098163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214415891881522801955398775 321623837822284202933098163)
          ·
            refine ⟨482435756733426304399647245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321623837822284202933098163 482435756733426304399647245)
            ·
              refine ⟨180913408775034864149867717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 482435756733426304399647245 180913408775034864149867717)
              ·
                refine ⟨33921264145319037028100197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180913408775034864149867717 33921264145319037028100197)
                ·
                  refine ⟨6360237027247319442768787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33921264145319037028100197 6360237027247319442768787)
                  ·
                    refine ⟨9540355540870979164153181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6360237027247319442768787 9540355540870979164153181)
                    ·
                      refine ⟨3577633327826617186557443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9540355540870979164153181 3577633327826617186557443)
                      ·
                        rfl

theorem cell23_6967416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 4, 1, 3].length) (baseStart_6967416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967416 prefixEnd_6967416 := by exact prefixLift 6967416
  have htrace : WordTrace (prefixWord ++ tailWord_6967416) baseStart_6967416 baseEnd_6967416 := by
    simpa [prefixWord, tailWord_6967416, baseEnd_6967416] using wordTrace_append hprefix tailTrace_6967416
  have hstable : (prefixWord ++ tailWord_6967416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967416).length < 2 ^ (prefixWord ++ tailWord_6967416).sum := by decide
  have hdescent : baseEnd_6967416 < baseStart_6967416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967417 : List Nat := [1, 2, 1, 3, 4, 2, 2, 3, 1, 2, 2]
def baseStart_6967417 : Nat := 118140960795 + 6967417 * 2 ^ 59
def prefixEnd_6967417 : Nat := 4983230072969 + 3 ^ 40 * 6967417 * 2
def baseEnd_6967417 : Nat := 3577633841307271682644939

theorem tailTrace_6967417 : CollatzResearch.WordTrace tailWord_6967417 prefixEnd_6967417 3577633841307271682644939 := by
  unfold tailWord_6967417
  simp only [CollatzResearch.WordTrace]
  refine ⟨254122574999245623932740505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169415049999497082621827003 254122574999245623932740505)
  ·
    refine ⟨190591931249434217949555379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254122574999245623932740505 190591931249434217949555379)
    ·
      refine ⟨285887896874151326924333069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190591931249434217949555379 285887896874151326924333069)
      ·
        refine ⟨107207961327806747596624901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285887896874151326924333069 107207961327806747596624901)
        ·
          refine ⟨20101492748963765174367169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107207961327806747596624901 20101492748963765174367169)
          ·
            refine ⟨15076119561722823880775377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20101492748963765174367169 15076119561722823880775377)
            ·
              refine ⟨11307089671292117910581533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15076119561722823880775377 11307089671292117910581533)
              ·
                refine ⟨4240158626734544216468075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11307089671292117910581533 4240158626734544216468075)
                ·
                  refine ⟨6360237940101816324702113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4240158626734544216468075 6360237940101816324702113)
                  ·
                    refine ⟨4770178455076362243526585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6360237940101816324702113 4770178455076362243526585)
                    ·
                      refine ⟨3577633841307271682644939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4770178455076362243526585 3577633841307271682644939)
                      ·
                        rfl

theorem cell23_6967417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 3, 1, 2, 2].length) (baseStart_6967417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967417 prefixEnd_6967417 := by exact prefixLift 6967417
  have htrace : WordTrace (prefixWord ++ tailWord_6967417) baseStart_6967417 baseEnd_6967417 := by
    simpa [prefixWord, tailWord_6967417, baseEnd_6967417] using wordTrace_append hprefix tailTrace_6967417
  have hstable : (prefixWord ++ tailWord_6967417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967417).length < 2 ^ (prefixWord ++ tailWord_6967417).sum := by decide
  have hdescent : baseEnd_6967417 < baseStart_6967417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967420 : List Nat := [2, 2, 2, 1, 1, 6, 2, 1, 1, 2, 3]
def baseStart_6967420 : Nat := 118140960795 + 6967420 * 2 ^ 59
def prefixEnd_6967420 : Nat := 4983230072969 + 3 ^ 40 * 6967420 * 2
def baseEnd_6967420 : Nat := 3577635381749235170907425

theorem tailTrace_6967420 : CollatzResearch.WordTrace tailWord_6967420 prefixEnd_6967420 3577635381749235170907425 := by
  unfold tailWord_6967420
  simp only [CollatzResearch.WordTrace]
  refine ⟨127061342209117377722549857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169415122945489836963399809 127061342209117377722549857)
  ·
    refine ⟨95296006656838033291912393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127061342209117377722549857 95296006656838033291912393)
    ·
      refine ⟨71472004992628524968934295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95296006656838033291912393 71472004992628524968934295)
      ·
        refine ⟨107208007488942787453401443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71472004992628524968934295 107208007488942787453401443)
        ·
          refine ⟨160812011233414181180102165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107208007488942787453401443 160812011233414181180102165)
          ·
            refine ⟨7538063026566289742817289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 160812011233414181180102165 7538063026566289742817289)
            ·
              refine ⟨5653547269924717307112967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7538063026566289742817289 5653547269924717307112967)
              ·
                refine ⟨8480320904887075960669451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5653547269924717307112967 8480320904887075960669451)
                ·
                  refine ⟨12720481357330613941004177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8480320904887075960669451 12720481357330613941004177)
                  ·
                    refine ⟨9540361017997960455753133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12720481357330613941004177 9540361017997960455753133)
                    ·
                      refine ⟨3577635381749235170907425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9540361017997960455753133 3577635381749235170907425)
                      ·
                        rfl

theorem cell23_6967420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 1, 2, 3].length) (baseStart_6967420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967420 prefixEnd_6967420 := by exact prefixLift 6967420
  have htrace : WordTrace (prefixWord ++ tailWord_6967420) baseStart_6967420 baseEnd_6967420 := by
    simpa [prefixWord, tailWord_6967420, baseEnd_6967420] using wordTrace_append hprefix tailTrace_6967420
  have hstable : (prefixWord ++ tailWord_6967420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967420).length < 2 ^ (prefixWord ++ tailWord_6967420).sum := by decide
  have hdescent : baseEnd_6967420 < baseStart_6967420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967450 : List Nat := [3, 1, 1, 5, 2, 2, 1, 1, 1, 3, 3]
def baseStart_6967450 : Nat := 118140960795 + 6967450 * 2 ^ 59
def prefixEnd_6967450 : Nat := 4983230072969 + 3 ^ 40 * 6967450 * 2
def baseEnd_6967450 : Nat := 3577650786168870053532287

theorem tailTrace_6967450 : CollatzResearch.WordTrace tailWord_6967450 prefixEnd_6967450 3577650786168870053532287 := by
  unfold tailWord_6967450
  simp only [CollatzResearch.WordTrace]
  refine ⟨63530944652031517642172951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169415852405417380379127869 63530944652031517642172951)
  ·
    refine ⟨95296416978047276463259427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63530944652031517642172951 95296416978047276463259427)
    ·
      refine ⟨142944625467070914694889141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95296416978047276463259427 142944625467070914694889141)
      ·
        refine ⟨13401058637537898252645857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142944625467070914694889141 13401058637537898252645857)
        ·
          refine ⟨10050793978153423689484393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13401058637537898252645857 10050793978153423689484393)
          ·
            refine ⟨7538095483615067767113295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10050793978153423689484393 7538095483615067767113295)
            ·
              refine ⟨11307143225422601650669943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7538095483615067767113295 11307143225422601650669943)
              ·
                refine ⟨16960714838133902476004915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11307143225422601650669943 16960714838133902476004915)
                ·
                  refine ⟨25441072257200853714007373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16960714838133902476004915 25441072257200853714007373)
                  ·
                    refine ⟨9540402096450320142752765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25441072257200853714007373 9540402096450320142752765)
                    ·
                      refine ⟨3577650786168870053532287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9540402096450320142752765 3577650786168870053532287)
                      ·
                        rfl

theorem cell23_6967450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_6967450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967450 prefixEnd_6967450 := by exact prefixLift 6967450
  have htrace : WordTrace (prefixWord ++ tailWord_6967450) baseStart_6967450 baseEnd_6967450 := by
    simpa [prefixWord, tailWord_6967450, baseEnd_6967450] using wordTrace_append hprefix tailTrace_6967450
  have hstable : (prefixWord ++ tailWord_6967450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967450).length < 2 ^ (prefixWord ++ tailWord_6967450).sum := by decide
  have hdescent : baseEnd_6967450 < baseStart_6967450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967519 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 7]
def baseStart_6967519 : Nat := 118140960795 + 6967519 * 2 ^ 59
def prefixEnd_6967519 : Nat := 4983230072969 + 3 ^ 40 * 6967519 * 2
def baseEnd_6967519 : Nat := 3577686216334030283569469

theorem tailTrace_6967519 : CollatzResearch.WordTrace tailWord_6967519 prefixEnd_6967519 3577686216334030283569469 := by
  unfold tailWord_6967519
  simp only [CollatzResearch.WordTrace]
  refine ⟨254126295244876095352953611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169417530163250730235302407 254126295244876095352953611)
  ·
    refine ⟨381189442867314143029430417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254126295244876095352953611 381189442867314143029430417)
    ·
      refine ⟨285892082150485607272072813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381189442867314143029430417 285892082150485607272072813)
      ·
        refine ⟨107209530806432102727027305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285892082150485607272072813 107209530806432102727027305)
        ·
          refine ⟨80407148104824077045270479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107209530806432102727027305 80407148104824077045270479)
          ·
            refine ⟨120610722157236115567905719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80407148104824077045270479 120610722157236115567905719)
            ·
              refine ⟨180916083235854173351858579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120610722157236115567905719 180916083235854173351858579)
              ·
                refine ⟨271374124853781260027787869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180916083235854173351858579 271374124853781260027787869)
                ·
                  refine ⟨101765296820167972510420451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 271374124853781260027787869 101765296820167972510420451)
                  ·
                    refine ⟨152647945230251958765630677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101765296820167972510420451 152647945230251958765630677)
                    ·
                      refine ⟨3577686216334030283569469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152647945230251958765630677 3577686216334030283569469)
                      ·
                        rfl

theorem cell23_6967519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_6967519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967519 prefixEnd_6967519 := by exact prefixLift 6967519
  have htrace : WordTrace (prefixWord ++ tailWord_6967519) baseStart_6967519 baseEnd_6967519 := by
    simpa [prefixWord, tailWord_6967519, baseEnd_6967519] using wordTrace_append hprefix tailTrace_6967519
  have hstable : (prefixWord ++ tailWord_6967519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967519).length < 2 ^ (prefixWord ++ tailWord_6967519).sum := by decide
  have hdescent : baseEnd_6967519 < baseStart_6967519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967563 : List Nat := [1, 1, 1, 1, 5, 2, 3, 1, 2, 4, 2]
def baseStart_6967563 : Nat := 118140960795 + 6967563 * 2 ^ 59
def prefixEnd_6967563 : Nat := 4983230072969 + 3 ^ 40 * 6967563 * 2
def baseEnd_6967563 : Nat := 3577708809482828111419267

theorem tailTrace_6967563 : CollatzResearch.WordTrace tailWord_6967563 prefixEnd_6967563 3577708809482828111419267 := by
  unfold tailWord_6967563
  simp only [CollatzResearch.WordTrace]
  refine ⟨254127900056716690867555343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169418600037811127245036895 254127900056716690867555343)
  ·
    refine ⟨381191850085075036301333015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254127900056716690867555343 381191850085075036301333015)
    ·
      refine ⟨571787775127612554451999523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381191850085075036301333015 571787775127612554451999523)
      ·
        refine ⟨857681662691418831677999285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571787775127612554451999523 857681662691418831677999285)
        ·
          refine ⟨80407655877320515469812433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 857681662691418831677999285 80407655877320515469812433)
          ·
            refine ⟨60305741907990386602359325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80407655877320515469812433 60305741907990386602359325)
            ·
              refine ⟨22614653215496394975884747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60305741907990386602359325 22614653215496394975884747)
              ·
                refine ⟨33921979823244592463827121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22614653215496394975884747 33921979823244592463827121)
                ·
                  refine ⟨25441484867433444347870341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33921979823244592463827121 25441484867433444347870341)
                  ·
                    refine ⟨4770278412643770815225689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25441484867433444347870341 4770278412643770815225689)
                    ·
                      refine ⟨3577708809482828111419267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4770278412643770815225689 3577708809482828111419267)
                      ·
                        rfl

theorem cell23_6967563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 4, 2].length) (baseStart_6967563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967563 prefixEnd_6967563 := by exact prefixLift 6967563
  have htrace : WordTrace (prefixWord ++ tailWord_6967563) baseStart_6967563 baseEnd_6967563 := by
    simpa [prefixWord, tailWord_6967563, baseEnd_6967563] using wordTrace_append hprefix tailTrace_6967563
  have hstable : (prefixWord ++ tailWord_6967563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967563).length < 2 ^ (prefixWord ++ tailWord_6967563).sum := by decide
  have hdescent : baseEnd_6967563 < baseStart_6967563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967583 : List Nat := [1, 1, 2, 4, 3, 2, 1, 1, 1, 4, 3]
def baseStart_6967583 : Nat := 118140960795 + 6967583 * 2 ^ 59
def prefixEnd_6967583 : Nat := 4983230072969 + 3 ^ 40 * 6967583 * 2
def baseEnd_6967583 : Nat := 3577719079095918033169175

theorem tailTrace_6967583 : CollatzResearch.WordTrace tailWord_6967583 prefixEnd_6967583 3577719079095918033169175 := by
  unfold tailWord_6967583
  simp only [CollatzResearch.WordTrace]
  refine ⟨254128629516644234283283403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169419086344429489522188935 254128629516644234283283403)
  ·
    refine ⟨381192944274966351424925105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254128629516644234283283403 381192944274966351424925105)
    ·
      refine ⟨285894708206224763568693829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381192944274966351424925105 285894708206224763568693829)
      ·
        refine ⟨53605257788667143169130093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 285894708206224763568693829 53605257788667143169130093)
        ·
          refine ⟨20101971670750178688423785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53605257788667143169130093 20101971670750178688423785)
          ·
            refine ⟨15076478753062634016317839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20101971670750178688423785 15076478753062634016317839)
            ·
              refine ⟨22614718129593951024476759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15076478753062634016317839 22614718129593951024476759)
              ·
                refine ⟨33922077194390926536715139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22614718129593951024476759 33922077194390926536715139)
                ·
                  refine ⟨50883115791586389805072709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33922077194390926536715139 50883115791586389805072709)
                  ·
                    refine ⟨9540584210922448088451133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50883115791586389805072709 9540584210922448088451133)
                    ·
                      refine ⟨3577719079095918033169175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9540584210922448088451133 3577719079095918033169175)
                      ·
                        rfl

theorem cell23_6967583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_6967583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967583 prefixEnd_6967583 := by exact prefixLift 6967583
  have htrace : WordTrace (prefixWord ++ tailWord_6967583) baseStart_6967583 baseEnd_6967583 := by
    simpa [prefixWord, tailWord_6967583, baseEnd_6967583] using wordTrace_append hprefix tailTrace_6967583
  have hstable : (prefixWord ++ tailWord_6967583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967583).length < 2 ^ (prefixWord ++ tailWord_6967583).sum := by decide
  have hdescent : baseEnd_6967583 < baseStart_6967583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967616 : List Nat := [2, 1, 1, 2, 2, 1, 2, 4, 3, 5]
def baseStart_6967616 : Nat := 118140960795 + 6967616 * 2 ^ 59
def prefixEnd_6967616 : Nat := 4983230072969 + 3 ^ 40 * 6967616 * 2
def baseEnd_6967616 : Nat := 1192578674652505468018841

theorem tailTrace_6967616 : CollatzResearch.WordTrace tailWord_6967616 prefixEnd_6967616 1192578674652505468018841 := by
  unfold tailWord_6967616
  simp only [CollatzResearch.WordTrace]
  refine ⟨127064916562762340459617351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169419888750349787279489801 127064916562762340459617351)
  ·
    refine ⟨190597374844143510689426027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127064916562762340459617351 190597374844143510689426027)
    ·
      refine ⟨285896062266215266034139041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190597374844143510689426027 285896062266215266034139041)
      ·
        refine ⟨214422046699661449525604281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285896062266215266034139041 214422046699661449525604281)
        ·
          refine ⟨160816535024746087144203211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214422046699661449525604281 160816535024746087144203211)
          ·
            refine ⟨241224802537119130716304817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160816535024746087144203211 241224802537119130716304817)
            ·
              refine ⟨180918601902839348037228613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241224802537119130716304817 180918601902839348037228613)
              ·
                refine ⟨33922237856782377756980365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180918601902839348037228613 33922237856782377756980365)
                ·
                  refine ⟨12720839196293391658867637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33922237856782377756980365 12720839196293391658867637)
                  ·
                    refine ⟨1192578674652505468018841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12720839196293391658867637 1192578674652505468018841)
                    ·
                      rfl

theorem cell23_6967616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 3, 5].length) (baseStart_6967616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967616 prefixEnd_6967616 := by exact prefixLift 6967616
  have htrace : WordTrace (prefixWord ++ tailWord_6967616) baseStart_6967616 baseEnd_6967616 := by
    simpa [prefixWord, tailWord_6967616, baseEnd_6967616] using wordTrace_append hprefix tailTrace_6967616
  have hstable : (prefixWord ++ tailWord_6967616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967616).length < 2 ^ (prefixWord ++ tailWord_6967616).sum := by decide
  have hdescent : baseEnd_6967616 < baseStart_6967616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967623 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 3, 5, 2]
def baseStart_6967623 : Nat := 118140960795 + 6967623 * 2 ^ 59
def prefixEnd_6967623 : Nat := 4983230072969 + 3 ^ 40 * 6967623 * 2
def baseEnd_6967623 : Nat := 3577739618322097876668991

theorem tailTrace_6967623 : CollatzResearch.WordTrace tailWord_6967623 prefixEnd_6967623 3577739618322097876668991 := by
  unfold tailWord_6967623
  simp only [CollatzResearch.WordTrace]
  refine ⟨254130088436499321114739523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169420058957666214076493015 254130088436499321114739523)
  ·
    refine ⟨381195132654748981672109285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254130088436499321114739523 381195132654748981672109285)
    ·
      refine ⟨71474087372765434063520491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 381195132654748981672109285 71474087372765434063520491)
      ·
        refine ⟨107211131059148151095280737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71474087372765434063520491 107211131059148151095280737)
        ·
          refine ⟨80408348294361113321460553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107211131059148151095280737 80408348294361113321460553)
          ·
            refine ⟨60306261220770834991095415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80408348294361113321460553 60306261220770834991095415)
            ·
              refine ⟨90459391831156252486643123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60306261220770834991095415 90459391831156252486643123)
              ·
                refine ⟨135689087746734378729964685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90459391831156252486643123 135689087746734378729964685)
                ·
                  refine ⟨50883407905025392023736757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135689087746734378729964685 50883407905025392023736757)
                  ·
                    refine ⟨4770319491096130502225321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50883407905025392023736757 4770319491096130502225321)
                    ·
                      refine ⟨3577739618322097876668991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4770319491096130502225321 3577739618322097876668991)
                      ·
                        rfl

theorem cell23_6967623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 5, 2].length) (baseStart_6967623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967623 prefixEnd_6967623 := by exact prefixLift 6967623
  have htrace : WordTrace (prefixWord ++ tailWord_6967623) baseStart_6967623 baseEnd_6967623 := by
    simpa [prefixWord, tailWord_6967623, baseEnd_6967623] using wordTrace_append hprefix tailTrace_6967623
  have hstable : (prefixWord ++ tailWord_6967623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967623).length < 2 ^ (prefixWord ++ tailWord_6967623).sum := by decide
  have hdescent : baseEnd_6967623 < baseStart_6967623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967633 : List Nat := [1, 2, 2, 1, 4, 2, 1, 4, 1, 5]
def baseStart_6967633 : Nat := 118140960795 + 6967633 * 2 ^ 59
def prefixEnd_6967633 : Nat := 4983230072969 + 3 ^ 40 * 6967633 * 2
def baseEnd_6967633 : Nat := 1192581584376214279181315

theorem tailTrace_6967633 : CollatzResearch.WordTrace tailWord_6967633 prefixEnd_6967633 1192581584376214279181315 := by
  unfold tailWord_6967633
  simp only [CollatzResearch.WordTrace]
  refine ⟨254130453166463092822603553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169420302110975395215069035 254130453166463092822603553)
  ·
    refine ⟨190597839874847319616952665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254130453166463092822603553 190597839874847319616952665)
    ·
      refine ⟨142948379906135489712714499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190597839874847319616952665 142948379906135489712714499)
      ·
        refine ⟨214422569859203234569071749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142948379906135489712714499 214422569859203234569071749)
        ·
          refine ⟨40204231848600606481700953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214422569859203234569071749 40204231848600606481700953)
          ·
            refine ⟨30153173886450454861275715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40204231848600606481700953 30153173886450454861275715)
            ·
              refine ⟨45229760829675682291913573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30153173886450454861275715 45229760829675682291913573)
              ·
                refine ⟨8480580155564190429733795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45229760829675682291913573 8480580155564190429733795)
                ·
                  refine ⟨12720870233346285644600693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8480580155564190429733795 12720870233346285644600693)
                  ·
                    refine ⟨1192581584376214279181315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12720870233346285644600693 1192581584376214279181315)
                    ·
                      rfl

theorem cell23_6967633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 5].length) (baseStart_6967633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967633 prefixEnd_6967633 := by exact prefixLift 6967633
  have htrace : WordTrace (prefixWord ++ tailWord_6967633) baseStart_6967633 baseEnd_6967633 := by
    simpa [prefixWord, tailWord_6967633, baseEnd_6967633] using wordTrace_append hprefix tailTrace_6967633
  have hstable : (prefixWord ++ tailWord_6967633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967633).length < 2 ^ (prefixWord ++ tailWord_6967633).sum := by decide
  have hdescent : baseEnd_6967633 < baseStart_6967633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967647 : List Nat := [1, 1, 2, 3, 1, 2, 5, 3, 1, 1, 3]
def baseStart_6967647 : Nat := 118140960795 + 6967647 * 2 ^ 59
def prefixEnd_6967647 : Nat := 4983230072969 + 3 ^ 40 * 6967647 * 2
def baseEnd_6967647 : Nat := 3577751941857805782768881

theorem tailTrace_6967647 : CollatzResearch.WordTrace tailWord_6967647 prefixEnd_6967647 3577751941857805782768881 := by
  unfold tailWord_6967647
  simp only [CollatzResearch.WordTrace]
  refine ⟨254130963788412373213613195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169420642525608248809075463 254130963788412373213613195)
  ·
    refine ⟨381196445682618559820419793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254130963788412373213613195 381196445682618559820419793)
    ·
      refine ⟨285897334261963919865314845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381196445682618559820419793 285897334261963919865314845)
      ·
        refine ⟨107211500348236469949493067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285897334261963919865314845 107211500348236469949493067)
        ·
          refine ⟨160817250522354704924239601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107211500348236469949493067 160817250522354704924239601)
          ·
            refine ⟨120612937891766028693179701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160817250522354704924239601 120612937891766028693179701)
            ·
              refine ⟨11307462927353065189985597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120612937891766028693179701 11307462927353065189985597)
              ·
                refine ⟨4240298597757399446244599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11307462927353065189985597 4240298597757399446244599)
                ·
                  refine ⟨6360447896636099169366899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4240298597757399446244599 6360447896636099169366899)
                  ·
                    refine ⟨9540671844954148754050349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6360447896636099169366899 9540671844954148754050349)
                    ·
                      refine ⟨3577751941857805782768881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9540671844954148754050349 3577751941857805782768881)
                      ·
                        rfl

theorem cell23_6967647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 3, 1, 1, 3].length) (baseStart_6967647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967647 prefixEnd_6967647 := by exact prefixLift 6967647
  have htrace : WordTrace (prefixWord ++ tailWord_6967647) baseStart_6967647 baseEnd_6967647 := by
    simpa [prefixWord, tailWord_6967647, baseEnd_6967647] using wordTrace_append hprefix tailTrace_6967647
  have hstable : (prefixWord ++ tailWord_6967647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967647).length < 2 ^ (prefixWord ++ tailWord_6967647).sum := by decide
  have hdescent : baseEnd_6967647 < baseStart_6967647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967650 : List Nat := [3, 3, 2, 1, 1, 2, 2, 3, 1, 5]
def baseStart_6967650 : Nat := 118140960795 + 6967650 * 2 ^ 59
def prefixEnd_6967650 : Nat := 4983230072969 + 3 ^ 40 * 6967650 * 2
def baseEnd_6967650 : Nat := 1192584494099923090343789

theorem tailTrace_6967650 : CollatzResearch.WordTrace tailWord_6967650 prefixEnd_6967650 1192584494099923090343789 := by
  unfold tailWord_6967650
  simp only [CollatzResearch.WordTrace]
  refine ⟨63532768301850376181493101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169420715471601003150648269 63532768301850376181493101)
  ·
    refine ⟨23824788113193891068059913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63532768301850376181493101 23824788113193891068059913)
    ·
      refine ⟨17868591084895418301044935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23824788113193891068059913 17868591084895418301044935)
      ·
        refine ⟨26802886627343127451567403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17868591084895418301044935 26802886627343127451567403)
        ·
          refine ⟨40204329941014691177351105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26802886627343127451567403 40204329941014691177351105)
          ·
            refine ⟨30153247455761018383013329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40204329941014691177351105 30153247455761018383013329)
            ·
              refine ⟨22614935591820763787259997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30153247455761018383013329 22614935591820763787259997)
              ·
                refine ⟨8480600846932786420222499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22614935591820763787259997 8480600846932786420222499)
                ·
                  refine ⟨12720901270399179630333749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8480600846932786420222499 12720901270399179630333749)
                  ·
                    refine ⟨1192584494099923090343789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12720901270399179630333749 1192584494099923090343789)
                    ·
                      rfl

theorem cell23_6967650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_6967650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967650 prefixEnd_6967650 := by exact prefixLift 6967650
  have htrace : WordTrace (prefixWord ++ tailWord_6967650) baseStart_6967650 baseEnd_6967650 := by
    simpa [prefixWord, tailWord_6967650, baseEnd_6967650] using wordTrace_append hprefix tailTrace_6967650
  have hstable : (prefixWord ++ tailWord_6967650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967650).length < 2 ^ (prefixWord ++ tailWord_6967650).sum := by decide
  have hdescent : baseEnd_6967650 < baseStart_6967650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967664 : List Nat := [2, 1, 1, 1, 4, 4, 3, 2, 1, 1, 3]
def baseStart_6967664 : Nat := 118140960795 + 6967664 * 2 ^ 59
def prefixEnd_6967664 : Nat := 4983230072969 + 3 ^ 40 * 6967664 * 2
def baseEnd_6967664 : Nat := 3577760671028932216256303

theorem tailTrace_6967664 : CollatzResearch.WordTrace tailWord_6967664 prefixEnd_6967664 3577760671028932216256303 := by
  unfold tailWord_6967664
  simp only [CollatzResearch.WordTrace]
  refine ⟨127065791914675392558491023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169421055886233856744654697 127065791914675392558491023)
  ·
    refine ⟨190598687872013088837736535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127065791914675392558491023 190598687872013088837736535)
    ·
      refine ⟨285898031808019633256604803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190598687872013088837736535 285898031808019633256604803)
      ·
        refine ⟨428847047712029449884907205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285898031808019633256604803 428847047712029449884907205)
        ·
          refine ⟨80408821446005521853420101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 428847047712029449884907205 80408821446005521853420101)
          ·
            refine ⟨15076654021126035347516269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80408821446005521853420101 15076654021126035347516269)
            ·
              refine ⟨5653745257922263255318601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15076654021126035347516269 5653745257922263255318601)
              ·
                refine ⟨4240308943441697441488951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5653745257922263255318601 4240308943441697441488951)
                ·
                  refine ⟨6360463415162546162233427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4240308943441697441488951 6360463415162546162233427)
                  ·
                    refine ⟨9540695122743819243350141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6360463415162546162233427 9540695122743819243350141)
                    ·
                      refine ⟨3577760671028932216256303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9540695122743819243350141 3577760671028932216256303)
                      ·
                        rfl

theorem cell23_6967664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 2, 1, 1, 3].length) (baseStart_6967664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967664 prefixEnd_6967664 := by exact prefixLift 6967664
  have htrace : WordTrace (prefixWord ++ tailWord_6967664) baseStart_6967664 baseEnd_6967664 := by
    simpa [prefixWord, tailWord_6967664, baseEnd_6967664] using wordTrace_append hprefix tailTrace_6967664
  have hstable : (prefixWord ++ tailWord_6967664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967664).length < 2 ^ (prefixWord ++ tailWord_6967664).sum := by decide
  have hdescent : baseEnd_6967664 < baseStart_6967664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967673 : List Nat := [1, 2, 1, 3, 2, 1, 1, 4, 3, 2, 3]
def baseStart_6967673 : Nat := 118140960795 + 6967673 * 2 ^ 59
def prefixEnd_6967673 : Nat := 4983230072969 + 3 ^ 40 * 6967673 * 2
def baseEnd_6967673 : Nat := 3577765292354822681043761

theorem tailTrace_6967673 : CollatzResearch.WordTrace tailWord_6967673 prefixEnd_6967673 3577765292354822681043761 := by
  unfold tailWord_6967673
  simp only [CollatzResearch.WordTrace]
  refine ⟨254131912086318179654059673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169421274724212119769373115 254131912086318179654059673)
  ·
    refine ⟨190598934064738634740544755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254131912086318179654059673 190598934064738634740544755)
    ·
      refine ⟨285898401097107952110817133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190598934064738634740544755 285898401097107952110817133)
      ·
        refine ⟨107211900411415482041556425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285898401097107952110817133 107211900411415482041556425)
        ·
          refine ⟨80408925308561611531167319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107211900411415482041556425 80408925308561611531167319)
          ·
            refine ⟨120613387962842417296750979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80408925308561611531167319 120613387962842417296750979)
            ·
              refine ⟨180920081944263625945126469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120613387962842417296750979 180920081944263625945126469)
              ·
                refine ⟨33922515364549429864711213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180920081944263625945126469 33922515364549429864711213)
                ·
                  refine ⟨12720943261706036199266705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33922515364549429864711213 12720943261706036199266705)
                  ·
                    refine ⟨9540707446279527149450029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12720943261706036199266705 9540707446279527149450029)
                    ·
                      refine ⟨3577765292354822681043761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9540707446279527149450029 3577765292354822681043761)
                      ·
                        rfl

theorem cell23_6967673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_6967673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967673 prefixEnd_6967673 := by exact prefixLift 6967673
  have htrace : WordTrace (prefixWord ++ tailWord_6967673) baseStart_6967673 baseEnd_6967673 := by
    simpa [prefixWord, tailWord_6967673, baseEnd_6967673] using wordTrace_append hprefix tailTrace_6967673
  have hstable : (prefixWord ++ tailWord_6967673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967673).length < 2 ^ (prefixWord ++ tailWord_6967673).sum := by decide
  have hdescent : baseEnd_6967673 < baseStart_6967673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967703 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 3, 3, 3]
def baseStart_6967703 : Nat := 118140960795 + 6967703 * 2 ^ 59
def prefixEnd_6967703 : Nat := 4983230072969 + 3 ^ 40 * 6967703 * 2
def baseEnd_6967703 : Nat := 3577780696774457563668623

theorem tailTrace_6967703 : CollatzResearch.WordTrace tailWord_6967703 prefixEnd_6967703 3577780696774457563668623 := by
  unfold tailWord_6967703
  simp only [CollatzResearch.WordTrace]
  refine ⟨254133006276209494777651763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169422004184139663185101175 254133006276209494777651763)
  ·
    refine ⟨381199509414314242166477645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254133006276209494777651763 381199509414314242166477645)
    ·
      refine ⟨142949816030367840812429117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 381199509414314242166477645 142949816030367840812429117)
      ·
        refine ⟨53606181011387940304660919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142949816030367840812429117 53606181011387940304660919)
        ·
          refine ⟨80409271517081910456991379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53606181011387940304660919 80409271517081910456991379)
          ·
            refine ⟨120613907275622865685487069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80409271517081910456991379 120613907275622865685487069)
            ·
              refine ⟨45230215228358574632057651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120613907275622865685487069 45230215228358574632057651)
              ·
                refine ⟨67845322842537861948086477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45230215228358574632057651 67845322842537861948086477)
                ·
                  refine ⟨25441996065951698230532429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67845322842537861948086477 25441996065951698230532429)
                  ·
                    refine ⟨9540748524731886836449661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25441996065951698230532429 9540748524731886836449661)
                    ·
                      refine ⟨3577780696774457563668623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9540748524731886836449661 3577780696774457563668623)
                      ·
                        rfl

theorem cell23_6967703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_6967703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967703 prefixEnd_6967703 := by exact prefixLift 6967703
  have htrace : WordTrace (prefixWord ++ tailWord_6967703) baseStart_6967703 baseEnd_6967703 := by
    simpa [prefixWord, tailWord_6967703, baseEnd_6967703] using wordTrace_append hprefix tailTrace_6967703
  have hstable : (prefixWord ++ tailWord_6967703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967703).length < 2 ^ (prefixWord ++ tailWord_6967703).sum := by decide
  have hdescent : baseEnd_6967703 < baseStart_6967703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967730 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2]
def baseStart_6967730 : Nat := 118140960795 + 6967730 * 2 ^ 59
def prefixEnd_6967730 : Nat := 4983230072969 + 3 ^ 40 * 6967730 * 2
def baseEnd_6967730 : Nat := 3577794560752128958030999

theorem tailTrace_6967730 : CollatzResearch.WordTrace tailWord_6967730 prefixEnd_6967730 3577794560752128958030999 := by
  unfold tailWord_6967730
  simp only [CollatzResearch.WordTrace]
  refine ⟨63533497761777919597221161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169422660698074452259256429 63533497761777919597221161)
  ·
    refine ⟨47650123321333439697915871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63533497761777919597221161 47650123321333439697915871)
    ·
      refine ⟨71475184982000159546873807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47650123321333439697915871 71475184982000159546873807)
      ·
        refine ⟨107212777473000239320310711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71475184982000159546873807 107212777473000239320310711)
        ·
          refine ⟨160819166209500358980466067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107212777473000239320310711 160819166209500358980466067)
          ·
            refine ⟨241228749314250538470699101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160819166209500358980466067 241228749314250538470699101)
            ·
              refine ⟨90460780992843951926512163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241228749314250538470699101 90460780992843951926512163)
              ·
                refine ⟨135691171489265927889768245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90460780992843951926512163 135691171489265927889768245)
                ·
                  refine ⟨12721047327118680739665773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135691171489265927889768245 12721047327118680739665773)
                  ·
                    refine ⟨4770392747669505277374665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12721047327118680739665773 4770392747669505277374665)
                    ·
                      refine ⟨3577794560752128958030999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4770392747669505277374665 3577794560752128958030999)
                      ·
                        rfl

theorem cell23_6967730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2].length) (baseStart_6967730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967730 prefixEnd_6967730 := by exact prefixLift 6967730
  have htrace : WordTrace (prefixWord ++ tailWord_6967730) baseStart_6967730 baseEnd_6967730 := by
    simpa [prefixWord, tailWord_6967730, baseEnd_6967730] using wordTrace_append hprefix tailTrace_6967730
  have hstable : (prefixWord ++ tailWord_6967730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967730).length < 2 ^ (prefixWord ++ tailWord_6967730).sum := by decide
  have hdescent : baseEnd_6967730 < baseStart_6967730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967737 : List Nat := [1, 2, 1, 4, 3, 1, 2, 3, 2, 1, 3]
def baseStart_6967737 : Nat := 118140960795 + 6967737 * 2 ^ 59
def prefixEnd_6967737 : Nat := 4983230072969 + 3 ^ 40 * 6967737 * 2
def baseEnd_6967737 : Nat := 3577798155116710430643467

theorem tailTrace_6967737 : CollatzResearch.WordTrace tailWord_6967737 prefixEnd_6967737 3577798155116710430643467 := by
  unfold tailWord_6967737
  simp only [CollatzResearch.WordTrace]
  refine ⟨254134246358086318584389465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169422830905390879056259643 254134246358086318584389465)
  ·
    refine ⟨190600684768564738938292099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254134246358086318584389465 190600684768564738938292099)
    ·
      refine ⟨285901027152847108407438149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190600684768564738938292099 285901027152847108407438149)
      ·
        refine ⟨53606442591158832826394653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 285901027152847108407438149 53606442591158832826394653)
        ·
          refine ⟨20102415971684562309897995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53606442591158832826394653 20102415971684562309897995)
          ·
            refine ⟨30153623957526843464846993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20102415971684562309897995 30153623957526843464846993)
            ·
              refine ⟨22615217968145132598635245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30153623957526843464846993 22615217968145132598635245)
              ·
                refine ⟨8480706738054424724488217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22615217968145132598635245 8480706738054424724488217)
                ·
                  refine ⟨6360530053540818543366163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8480706738054424724488217 6360530053540818543366163)
                  ·
                    refine ⟨9540795080311227815049245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6360530053540818543366163 9540795080311227815049245)
                    ·
                      refine ⟨3577798155116710430643467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9540795080311227815049245 3577798155116710430643467)
                      ·
                        rfl

theorem cell23_6967737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_6967737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967737 prefixEnd_6967737 := by exact prefixLift 6967737
  have htrace : WordTrace (prefixWord ++ tailWord_6967737) baseStart_6967737 baseEnd_6967737 := by
    simpa [prefixWord, tailWord_6967737, baseEnd_6967737] using wordTrace_append hprefix tailTrace_6967737
  have hstable : (prefixWord ++ tailWord_6967737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967737).length < 2 ^ (prefixWord ++ tailWord_6967737).sum := by decide
  have hdescent : baseEnd_6967737 < baseStart_6967737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967764 : List Nat := [2, 4, 1, 2, 2, 2, 1, 3, 1, 3, 2]
def baseStart_6967764 : Nat := 118140960795 + 6967764 * 2 ^ 59
def prefixEnd_6967764 : Nat := 4983230072969 + 3 ^ 40 * 6967764 * 2
def baseEnd_6967764 : Nat := 3577812019094381825005843

theorem tailTrace_6967764 : CollatzResearch.WordTrace tailWord_6967764 prefixEnd_6967764 3577812019094381825005843 := by
  unfold tailWord_6967764
  simp only [CollatzResearch.WordTrace]
  refine ⟨127067615564494251097811173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169423487419325668130414897 127067615564494251097811173)
  ·
    refine ⟨23825177918342672080839595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127067615564494251097811173 23825177918342672080839595)
    ·
      refine ⟨35737766877514008121259393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23825177918342672080839595 35737766877514008121259393)
      ·
        refine ⟨26803325158135506090944545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35737766877514008121259393 26803325158135506090944545)
        ·
          refine ⟨20102493868601629568208409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26803325158135506090944545 20102493868601629568208409)
          ·
            refine ⟨15076870401451222176156307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20102493868601629568208409 15076870401451222176156307)
            ·
              refine ⟨22615305602176833264234461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15076870401451222176156307 22615305602176833264234461)
              ·
                refine ⟨8480739600816312474087923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22615305602176833264234461 8480739600816312474087923)
                ·
                  refine ⟨12721109401224468711131885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8480739600816312474087923 12721109401224468711131885)
                  ·
                    refine ⟨4770416025459175766674457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12721109401224468711131885 4770416025459175766674457)
                    ·
                      refine ⟨3577812019094381825005843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4770416025459175766674457 3577812019094381825005843)
                      ·
                        rfl

theorem cell23_6967764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_6967764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967764 prefixEnd_6967764 := by exact prefixLift 6967764
  have htrace : WordTrace (prefixWord ++ tailWord_6967764) baseStart_6967764 baseEnd_6967764 := by
    simpa [prefixWord, tailWord_6967764, baseEnd_6967764] using wordTrace_append hprefix tailTrace_6967764
  have hstable : (prefixWord ++ tailWord_6967764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967764).length < 2 ^ (prefixWord ++ tailWord_6967764).sum := by decide
  have hdescent : baseEnd_6967764 < baseStart_6967764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967777 : List Nat := [1, 2, 3, 1, 2, 2, 3, 1, 4, 2, 2]
def baseStart_6967777 : Nat := 118140960795 + 6967777 * 2 ^ 59
def prefixEnd_6967777 : Nat := 4983230072969 + 3 ^ 40 * 6967777 * 2
def baseEnd_6967777 : Nat := 3577818694342890274143283

theorem tailTrace_6967777 : CollatzResearch.WordTrace tailWord_6967777 prefixEnd_6967777 3577818694342890274143283 := by
  unfold tailWord_6967777
  simp only [CollatzResearch.WordTrace]
  refine ⟨254135705277941405415845585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169423803518627603610563723 254135705277941405415845585)
  ·
    refine ⟨190601778958456054061884189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254135705277941405415845585 190601778958456054061884189)
    ·
      refine ⟨71475667109421020273206571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190601778958456054061884189 71475667109421020273206571)
      ·
        refine ⟨107213500664131530409809857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71475667109421020273206571 107213500664131530409809857)
        ·
          refine ⟨80410125498098647807357393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107213500664131530409809857 80410125498098647807357393)
          ·
            refine ⟨60307594123573985855518045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80410125498098647807357393 60307594123573985855518045)
            ·
              refine ⟨22615347796340244695819267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60307594123573985855518045 22615347796340244695819267)
              ·
                refine ⟨33923021694510367043728901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22615347796340244695819267 33923021694510367043728901)
                ·
                  refine ⟨6360566567720693820699169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33923021694510367043728901 6360566567720693820699169)
                  ·
                    refine ⟨4770424925790520365524377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6360566567720693820699169 4770424925790520365524377)
                    ·
                      refine ⟨3577818694342890274143283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4770424925790520365524377 3577818694342890274143283)
                      ·
                        rfl

theorem cell23_6967777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 4, 2, 2].length) (baseStart_6967777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967777 prefixEnd_6967777 := by exact prefixLift 6967777
  have htrace : WordTrace (prefixWord ++ tailWord_6967777) baseStart_6967777 baseEnd_6967777 := by
    simpa [prefixWord, tailWord_6967777, baseEnd_6967777] using wordTrace_append hprefix tailTrace_6967777
  have hstable : (prefixWord ++ tailWord_6967777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967777).length < 2 ^ (prefixWord ++ tailWord_6967777).sum := by decide
  have hdescent : baseEnd_6967777 < baseStart_6967777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967790 : List Nat := [4, 1, 2, 1, 2, 2, 2, 1, 2, 2, 4]
def baseStart_6967790 : Nat := 118140960795 + 6967790 * 2 ^ 59
def prefixEnd_6967790 : Nat := 4983230072969 + 3 ^ 40 * 6967790 * 2
def baseEnd_6967790 : Nat := 3577825369591398723280723

theorem tailTrace_6967790 : CollatzResearch.WordTrace tailWord_6967790 prefixEnd_6967790 3577825369591398723280723 := by
  unfold tailWord_6967790
  simp only [CollatzResearch.WordTrace]
  refine ⟨31767022428361788579508603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169424119617929539090712549 31767022428361788579508603)
  ·
    refine ⟨47650533642542682869262905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31767022428361788579508603 47650533642542682869262905)
    ·
      refine ⟨35737900231907012151947179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47650533642542682869262905 35737900231907012151947179)
      ·
        refine ⟨53606850347860518227920769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35737900231907012151947179 53606850347860518227920769)
        ·
          refine ⟨40205137760895388670940577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53606850347860518227920769 40205137760895388670940577)
          ·
            refine ⟨30153853320671541503205433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40205137760895388670940577 30153853320671541503205433)
            ·
              refine ⟨22615389990503656127404075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30153853320671541503205433 22615389990503656127404075)
              ·
                refine ⟨33923084985755484191106113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22615389990503656127404075 33923084985755484191106113)
                ·
                  refine ⟨25442313739316613143329585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33923084985755484191106113 25442313739316613143329585)
                  ·
                    refine ⟨19081735304487459857497189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25442313739316613143329585 19081735304487459857497189)
                    ·
                      refine ⟨3577825369591398723280723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19081735304487459857497189 3577825369591398723280723)
                      ·
                        rfl

theorem cell23_6967790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_6967790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967790 prefixEnd_6967790 := by exact prefixLift 6967790
  have htrace : WordTrace (prefixWord ++ tailWord_6967790) baseStart_6967790 baseEnd_6967790 := by
    simpa [prefixWord, tailWord_6967790, baseEnd_6967790] using wordTrace_append hprefix tailTrace_6967790
  have hstable : (prefixWord ++ tailWord_6967790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967790).length < 2 ^ (prefixWord ++ tailWord_6967790).sum := by decide
  have hdescent : baseEnd_6967790 < baseStart_6967790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967813 : List Nat := [1, 3, 1, 1, 2, 2, 4, 1, 1, 7]
def baseStart_6967813 : Nat := 118140960795 + 6967813 * 2 ^ 59
def prefixEnd_6967813 : Nat := 4983230072969 + 3 ^ 40 * 6967813 * 2
def baseEnd_6967813 : Nat := 1192612393215484044431039

theorem tailTrace_6967813 : CollatzResearch.WordTrace tailWord_6967813 prefixEnd_6967813 1192612393215484044431039 := by
  unfold tailWord_6967813
  simp only [CollatzResearch.WordTrace]
  refine ⟨254137018305810983564156093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169424678870540655709437395 254137018305810983564156093)
  ·
    refine ⟨95301381864679118836558535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254137018305810983564156093 95301381864679118836558535)
    ·
      refine ⟨142952072797018678254837803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95301381864679118836558535 142952072797018678254837803)
      ·
        refine ⟨214428109195528017382256705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142952072797018678254837803 214428109195528017382256705)
        ·
          refine ⟨160821081896646013036692529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214428109195528017382256705 160821081896646013036692529)
          ·
            refine ⟨120615811422484509777519397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160821081896646013036692529 120615811422484509777519397)
            ·
              refine ⟨22615464641715845583284887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120615811422484509777519397 22615464641715845583284887)
              ·
                refine ⟨33923196962573768374927331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22615464641715845583284887 33923196962573768374927331)
                ·
                  refine ⟨50884795443860652562390997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33923196962573768374927331 50884795443860652562390997)
                  ·
                    refine ⟨1192612393215484044431039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50884795443860652562390997 1192612393215484044431039)
                    ·
                      rfl

theorem cell23_6967813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 7].length) (baseStart_6967813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967813 prefixEnd_6967813 := by exact prefixLift 6967813
  have htrace : WordTrace (prefixWord ++ tailWord_6967813) baseStart_6967813 baseEnd_6967813 := by
    simpa [prefixWord, tailWord_6967813, baseEnd_6967813] using wordTrace_append hprefix tailTrace_6967813
  have hstable : (prefixWord ++ tailWord_6967813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967813).length < 2 ^ (prefixWord ++ tailWord_6967813).sum := by decide
  have hdescent : baseEnd_6967813 < baseStart_6967813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967814 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_6967814 : Nat := 118140960795 + 6967814 * 2 ^ 59
def prefixEnd_6967814 : Nat := 4983230072969 + 3 ^ 40 * 6967814 * 2
def baseEnd_6967814 : Nat := 3577837693127106629380613

theorem tailTrace_6967814 : CollatzResearch.WordTrace tailWord_6967814 prefixEnd_6967814 3577837693127106629380613 := by
  unfold tailWord_6967814
  simp only [CollatzResearch.WordTrace]
  refine ⟨7941782961837730022966953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 169424703185871573823294997 7941782961837730022966953)
  ·
    refine ⟨5956337221378297517225215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7941782961837730022966953 5956337221378297517225215)
    ·
      refine ⟨8934505832067446275837823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5956337221378297517225215 8934505832067446275837823)
      ·
        refine ⟨13401758748101169413756735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8934505832067446275837823 13401758748101169413756735)
        ·
          refine ⟨20102638122151754120635103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13401758748101169413756735 20102638122151754120635103)
          ·
            refine ⟨30153957183227631180952655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20102638122151754120635103 30153957183227631180952655)
            ·
              refine ⟨45230935774841446771428983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30153957183227631180952655 45230935774841446771428983)
              ·
                refine ⟨67846403662262170157143475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45230935774841446771428983 67846403662262170157143475)
                ·
                  refine ⟨101769605493393255235715213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67846403662262170157143475 101769605493393255235715213)
                  ·
                    refine ⟨38163602060022470713393205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101769605493393255235715213 38163602060022470713393205)
                    ·
                      refine ⟨3577837693127106629380613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38163602060022470713393205 3577837693127106629380613)
                      ·
                        rfl

theorem cell23_6967814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_6967814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967814 prefixEnd_6967814 := by exact prefixLift 6967814
  have htrace : WordTrace (prefixWord ++ tailWord_6967814) baseStart_6967814 baseEnd_6967814 := by
    simpa [prefixWord, tailWord_6967814, baseEnd_6967814] using wordTrace_append hprefix tailTrace_6967814
  have hstable : (prefixWord ++ tailWord_6967814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967814).length < 2 ^ (prefixWord ++ tailWord_6967814).sum := by decide
  have hdescent : baseEnd_6967814 < baseStart_6967814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967913 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 1, 3, 7]
def baseStart_6967913 : Nat := 118140960795 + 6967913 * 2 ^ 59
def prefixEnd_6967913 : Nat := 4983230072969 + 3 ^ 40 * 6967913 * 2
def baseEnd_6967913 : Nat := 3577888527711901742042657

theorem tailTrace_6967913 : CollatzResearch.WordTrace tailWord_6967913 prefixEnd_6967913 3577888527711901742042657 := by
  unfold tailWord_6967913
  simp only [CollatzResearch.WordTrace]
  refine ⟨254140665605448700642796393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169427110403632467095197595 254140665605448700642796393)
  ·
    refine ⟨190605499204086525482097295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254140665605448700642796393 190605499204086525482097295)
    ·
      refine ⟨285908248806129788223145943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190605499204086525482097295 285908248806129788223145943)
      ·
        refine ⟨428862373209194682334718915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285908248806129788223145943 428862373209194682334718915)
        ·
          refine ⟨643293559813792023502078373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428862373209194682334718915 643293559813792023502078373)
          ·
            refine ⟨120617542465086004406639695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 643293559813792023502078373 120617542465086004406639695)
            ·
              refine ⟨180926313697629006609959543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120617542465086004406639695 180926313697629006609959543)
              ·
                refine ⟨271389470546443509914939315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180926313697629006609959543 271389470546443509914939315)
                ·
                  refine ⟨407084205819665264872408973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271389470546443509914939315 407084205819665264872408973)
                  ·
                    refine ⟨152656577182374474327153365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 407084205819665264872408973 152656577182374474327153365)
                    ·
                      refine ⟨3577888527711901742042657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152656577182374474327153365 3577888527711901742042657)
                      ·
                        rfl

theorem cell23_6967913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 3, 7].length) (baseStart_6967913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967913 prefixEnd_6967913 := by exact prefixLift 6967913
  have htrace : WordTrace (prefixWord ++ tailWord_6967913) baseStart_6967913 baseEnd_6967913 := by
    simpa [prefixWord, tailWord_6967913, baseEnd_6967913] using wordTrace_append hprefix tailTrace_6967913
  have hstable : (prefixWord ++ tailWord_6967913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967913).length < 2 ^ (prefixWord ++ tailWord_6967913).sum := by decide
  have hdescent : baseEnd_6967913 < baseStart_6967913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967937 : List Nat := [1, 2, 4, 2, 1, 1, 3, 3, 1, 5]
def baseStart_6967937 : Nat := 118140960795 + 6967937 * 2 ^ 59
def prefixEnd_6967937 : Nat := 4983230072969 + 3 ^ 40 * 6967937 * 2
def baseEnd_6967937 : Nat := 1192633617082536549380849

theorem tailTrace_6967937 : CollatzResearch.WordTrace tailWord_6967937 prefixEnd_6967937 1192633617082536549380849 := by
  unfold tailWord_6967937
  simp only [CollatzResearch.WordTrace]
  refine ⟨254141540957361752741670065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169427693971574501827780043 254141540957361752741670065)
  ·
    refine ⟨190606155718021314556252549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254141540957361752741670065 190606155718021314556252549)
    ·
      refine ⟨35738654197128996479297353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190606155718021314556252549 35738654197128996479297353)
      ·
        refine ⟨26803990647846747359473015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35738654197128996479297353 26803990647846747359473015)
        ·
          refine ⟨40205985971770121039209523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26803990647846747359473015 40205985971770121039209523)
          ·
            refine ⟨60308978957655181558814285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40205985971770121039209523 60308978957655181558814285)
            ·
              refine ⟨22615867109120693084555357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60308978957655181558814285 22615867109120693084555357)
              ·
                refine ⟨8480950165920259906708259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22615867109120693084555357 8480950165920259906708259)
                ·
                  refine ⟨12721425248880389860062389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8480950165920259906708259 12721425248880389860062389)
                  ·
                    refine ⟨1192633617082536549380849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12721425248880389860062389 1192633617082536549380849)
                    ·
                      rfl

theorem cell23_6967937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_6967937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967937 prefixEnd_6967937 := by exact prefixLift 6967937
  have htrace : WordTrace (prefixWord ++ tailWord_6967937) baseStart_6967937 baseEnd_6967937 := by
    simpa [prefixWord, tailWord_6967937, baseEnd_6967937] using wordTrace_append hprefix tailTrace_6967937
  have hstable : (prefixWord ++ tailWord_6967937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967937).length < 2 ^ (prefixWord ++ tailWord_6967937).sum := by decide
  have hdescent : baseEnd_6967937 < baseStart_6967937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967977 : List Nat := [1, 2, 1, 1, 1, 1, 2, 8, 1, 2, 3]
def baseStart_6967977 : Nat := 118140960795 + 6967977 * 2 ^ 59
def prefixEnd_6967977 : Nat := 4983230072969 + 3 ^ 40 * 6967977 * 2
def baseEnd_6967977 : Nat := 3577921390473789491642363

theorem tailTrace_6967977 : CollatzResearch.WordTrace tailWord_6967977 prefixEnd_6967977 3577921390473789491642363 := by
  unfold tailWord_6967977
  simp only [CollatzResearch.WordTrace]
  refine ⟨254142999877216839573126185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169428666584811226382084123 254142999877216839573126185)
  ·
    refine ⟨190607249907912629679844639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254142999877216839573126185 190607249907912629679844639)
    ·
      refine ⟨285910874861868944519766959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190607249907912629679844639 285910874861868944519766959)
      ·
        refine ⟨428866312292803416779650439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285910874861868944519766959 428866312292803416779650439)
        ·
          refine ⟨643299468439205125169475659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428866312292803416779650439 643299468439205125169475659)
          ·
            refine ⟨964949202658807687754213489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643299468439205125169475659 964949202658807687754213489)
            ·
              refine ⟨723711901994105765815660117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 964949202658807687754213489 723711901994105765815660117)
              ·
                refine ⟨8480998851493426943152267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 723711901994105765815660117 8480998851493426943152267)
                ·
                  refine ⟨12721498277240140414728401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8480998851493426943152267 12721498277240140414728401)
                  ·
                    refine ⟨9541123707930105311046301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12721498277240140414728401 9541123707930105311046301)
                    ·
                      refine ⟨3577921390473789491642363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9541123707930105311046301 3577921390473789491642363)
                      ·
                        rfl

theorem cell23_6967977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 2, 3].length) (baseStart_6967977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967977 prefixEnd_6967977 := by exact prefixLift 6967977
  have htrace : WordTrace (prefixWord ++ tailWord_6967977) baseStart_6967977 baseEnd_6967977 := by
    simpa [prefixWord, tailWord_6967977, baseEnd_6967977] using wordTrace_append hprefix tailTrace_6967977
  have hstable : (prefixWord ++ tailWord_6967977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967977).length < 2 ^ (prefixWord ++ tailWord_6967977).sum := by decide
  have hdescent : baseEnd_6967977 < baseStart_6967977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6967985 : List Nat := [1, 2, 2, 6, 1, 2, 1, 3, 1, 1, 3]
def baseStart_6967985 : Nat := 118140960795 + 6967985 * 2 ^ 59
def prefixEnd_6967985 : Nat := 4983230072969 + 3 ^ 40 * 6967985 * 2
def baseEnd_6967985 : Nat := 3577925498319025460342327

theorem tailTrace_6967985 : CollatzResearch.WordTrace tailWord_6967985 prefixEnd_6967985 3577925498319025460342327 := by
  unfold tailWord_6967985
  simp only [CollatzResearch.WordTrace]
  refine ⟨254143291661187856939417409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169428861107458571292944939 254143291661187856939417409)
  ·
    refine ⟨190607468745890892704563057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254143291661187856939417409 190607468745890892704563057)
    ·
      refine ⟨142955601559418169528422293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190607468745890892704563057 142955601559418169528422293)
      ·
        refine ⟨6701043823097726696644795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 142955601559418169528422293 6701043823097726696644795)
        ·
          refine ⟨10051565734646590044967193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6701043823097726696644795 10051565734646590044967193)
          ·
            refine ⟨7538674300984942533725395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10051565734646590044967193 7538674300984942533725395)
            ·
              refine ⟨11308011451477413800588093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7538674300984942533725395 11308011451477413800588093)
              ·
                refine ⟨4240504294304030175220535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11308011451477413800588093 4240504294304030175220535)
                ·
                  refine ⟨6360756441456045262830803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4240504294304030175220535 6360756441456045262830803)
                  ·
                    refine ⟨9541134662184067894246205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6360756441456045262830803 9541134662184067894246205)
                    ·
                      refine ⟨3577925498319025460342327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9541134662184067894246205 3577925498319025460342327)
                      ·
                        rfl

theorem cell23_6967985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_6967985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6967985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6967985 prefixEnd_6967985 := by exact prefixLift 6967985
  have htrace : WordTrace (prefixWord ++ tailWord_6967985) baseStart_6967985 baseEnd_6967985 := by
    simpa [prefixWord, tailWord_6967985, baseEnd_6967985] using wordTrace_append hprefix tailTrace_6967985
  have hstable : (prefixWord ++ tailWord_6967985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6967985).length < 2 ^ (prefixWord ++ tailWord_6967985).sum := by decide
  have hdescent : baseEnd_6967985 < baseStart_6967985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6967985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968018 : List Nat := [3, 2, 2, 2, 3, 2, 2, 1, 2, 4]
def baseStart_6968018 : Nat := 118140960795 + 6968018 * 2 ^ 59
def prefixEnd_6968018 : Nat := 4983230072969 + 3 ^ 40 * 6968018 * 2
def baseEnd_6968018 : Nat := 1192647481060207943743225

theorem tailTrace_6968018 : CollatzResearch.WordTrace tailWord_6968018 prefixEnd_6968018 1192647481060207943743225 := by
  unfold tailWord_6968018
  simp only [CollatzResearch.WordTrace]
  refine ⟨63536123817517075893842177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169429663513378869050245805 63536123817517075893842177)
  ·
    refine ⟨47652092863137806920381633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63536123817517075893842177 47652092863137806920381633)
    ·
      refine ⟨35739069647353355190286225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47652092863137806920381633 35739069647353355190286225)
      ·
        refine ⟨26804302235515016392714669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35739069647353355190286225 26804302235515016392714669)
        ·
          refine ⟨10051613338318131147268001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26804302235515016392714669 10051613338318131147268001)
          ·
            refine ⟨7538710003738598360451001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10051613338318131147268001 7538710003738598360451001)
            ·
              refine ⟨5654032502803948770338251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7538710003738598360451001 5654032502803948770338251)
              ·
                refine ⟨8481048754205923155507377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5654032502803948770338251 8481048754205923155507377)
                ·
                  refine ⟨6360786565654442366630533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8481048754205923155507377 6360786565654442366630533)
                  ·
                    refine ⟨1192647481060207943743225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6360786565654442366630533 1192647481060207943743225)
                    ·
                      rfl

theorem cell23_6968018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_6968018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968018 prefixEnd_6968018 := by exact prefixLift 6968018
  have htrace : WordTrace (prefixWord ++ tailWord_6968018) baseStart_6968018 baseEnd_6968018 := by
    simpa [prefixWord, tailWord_6968018, baseEnd_6968018] using wordTrace_append hprefix tailTrace_6968018
  have hstable : (prefixWord ++ tailWord_6968018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968018).length < 2 ^ (prefixWord ++ tailWord_6968018).sum := by decide
  have hdescent : baseEnd_6968018 < baseStart_6968018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968028 : List Nat := [2, 2, 5, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_6968028 : Nat := 118140960795 + 6968028 * 2 ^ 59
def prefixEnd_6968028 : Nat := 4983230072969 + 3 ^ 40 * 6968028 * 2
def baseEnd_6968028 : Nat := 3577947577987168792104629

theorem tailTrace_6968028 : CollatzResearch.WordTrace tailWord_6968028 prefixEnd_6968028 3577947577987168792104629 := by
  unfold tailWord_6968028
  simp only [CollatzResearch.WordTrace]
  refine ⟨127072430000016037641616369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169429906666688050188821825 127072430000016037641616369)
  ·
    refine ⟨95304322500012028231212277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127072430000016037641616369 95304322500012028231212277)
    ·
      refine ⟨8934780234376127646676151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95304322500012028231212277 8934780234376127646676151)
      ·
        refine ⟨13402170351564191470014227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8934780234376127646676151 13402170351564191470014227)
        ·
          refine ⟨20103255527346287205021341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13402170351564191470014227 20103255527346287205021341)
          ·
            refine ⟨7538720822754857701883003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20103255527346287205021341 7538720822754857701883003)
            ·
              refine ⟨11308081234132286552824505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7538720822754857701883003 11308081234132286552824505)
              ·
                refine ⟨8481060925599214914618379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11308081234132286552824505 8481060925599214914618379)
                ·
                  refine ⟨12721591388398822371927569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8481060925599214914618379 12721591388398822371927569)
                  ·
                    refine ⟨9541193541299116778945677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12721591388398822371927569 9541193541299116778945677)
                    ·
                      refine ⟨3577947577987168792104629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9541193541299116778945677 3577947577987168792104629)
                      ·
                        rfl

theorem cell23_6968028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_6968028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968028 prefixEnd_6968028 := by exact prefixLift 6968028
  have htrace : WordTrace (prefixWord ++ tailWord_6968028) baseStart_6968028 baseEnd_6968028 := by
    simpa [prefixWord, tailWord_6968028, baseEnd_6968028] using wordTrace_append hprefix tailTrace_6968028
  have hstable : (prefixWord ++ tailWord_6968028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968028).length < 2 ^ (prefixWord ++ tailWord_6968028).sum := by decide
  have hdescent : baseEnd_6968028 < baseStart_6968028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968081 : List Nat := [1, 2, 2, 1, 1, 3, 4, 3, 2, 2, 2]
def baseStart_6968081 : Nat := 118140960795 + 6968081 * 2 ^ 59
def prefixEnd_6968081 : Nat := 4983230072969 + 3 ^ 40 * 6968081 * 2
def baseEnd_6968081 : Nat := 3577974792461857084741885

theorem tailTrace_6968081 : CollatzResearch.WordTrace tailWord_6968081 prefixEnd_6968081 3577974792461857084741885 := by
  unfold tailWord_6968081
  simp only [CollatzResearch.WordTrace]
  refine ⟨254146793068840065334912097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169431195379226710223274731 254146793068840065334912097)
  ·
    refine ⟨190610094801630049001184073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254146793068840065334912097 190610094801630049001184073)
    ·
      refine ⟨142957571101222536750888055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190610094801630049001184073 142957571101222536750888055)
      ·
        refine ⟨214436356651833805126332083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142957571101222536750888055 214436356651833805126332083)
        ·
          refine ⟨321654534977750707689498125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214436356651833805126332083 321654534977750707689498125)
          ·
            refine ⟨120620450616656515383561797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 321654534977750707689498125 120620450616656515383561797)
            ·
              refine ⟨22616334490623096634417837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120620450616656515383561797 22616334490623096634417837)
              ·
                refine ⟨8481125433983661237906689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22616334490623096634417837 8481125433983661237906689)
                ·
                  refine ⟨6360844075487745928430017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8481125433983661237906689 6360844075487745928430017)
                  ·
                    refine ⟨4770633056615809446322513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6360844075487745928430017 4770633056615809446322513)
                    ·
                      refine ⟨3577974792461857084741885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4770633056615809446322513 3577974792461857084741885)
                      ·
                        rfl

theorem cell23_6968081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2, 2, 2].length) (baseStart_6968081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968081 prefixEnd_6968081 := by exact prefixLift 6968081
  have htrace : WordTrace (prefixWord ++ tailWord_6968081) baseStart_6968081 baseEnd_6968081 := by
    simpa [prefixWord, tailWord_6968081, baseEnd_6968081] using wordTrace_append hprefix tailTrace_6968081
  have hstable : (prefixWord ++ tailWord_6968081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968081).length < 2 ^ (prefixWord ++ tailWord_6968081).sum := by decide
  have hdescent : baseEnd_6968081 < baseStart_6968081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968097 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 1, 5, 3]
def baseStart_6968097 : Nat := 118140960795 + 6968097 * 2 ^ 59
def prefixEnd_6968097 : Nat := 4983230072969 + 3 ^ 40 * 6968097 * 2
def baseEnd_6968097 : Nat := 3577983008152329022141811

theorem tailTrace_6968097 : CollatzResearch.WordTrace tailWord_6968097 prefixEnd_6968097 3577983008152329022141811 := by
  unfold tailWord_6968097
  simp only [CollatzResearch.WordTrace]
  refine ⟨254147376636782100067494545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169431584424521400044996363 254147376636782100067494545)
  ·
    refine ⟨190610532477586575050620909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254147376636782100067494545 190610532477586575050620909)
    ·
      refine ⟨71478949679094965643982841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190610532477586575050620909 71478949679094965643982841)
      ·
        refine ⟨53609212259321224232987131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71478949679094965643982841 53609212259321224232987131)
        ·
          refine ⟨80413818388981836349480697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53609212259321224232987131 80413818388981836349480697)
          ·
            refine ⟨60310363791736377262110523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80413818388981836349480697 60310363791736377262110523)
            ·
              refine ⟨90465545687604565893165785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60310363791736377262110523 90465545687604565893165785)
              ·
                refine ⟨67849159265703424419874339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90465545687604565893165785 67849159265703424419874339)
                ·
                  refine ⟨101773738898555136629811509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67849159265703424419874339 101773738898555136629811509)
                  ·
                    refine ⟨9541288021739544059044829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101773738898555136629811509 9541288021739544059044829)
                    ·
                      refine ⟨3577983008152329022141811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9541288021739544059044829 3577983008152329022141811)
                      ·
                        rfl

theorem cell23_6968097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_6968097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968097 prefixEnd_6968097 := by exact prefixLift 6968097
  have htrace : WordTrace (prefixWord ++ tailWord_6968097) baseStart_6968097 baseEnd_6968097 := by
    simpa [prefixWord, tailWord_6968097, baseEnd_6968097] using wordTrace_append hprefix tailTrace_6968097
  have hstable : (prefixWord ++ tailWord_6968097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968097).length < 2 ^ (prefixWord ++ tailWord_6968097).sum := by decide
  have hdescent : baseEnd_6968097 < baseStart_6968097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968132 : List Nat := [2, 3, 4, 2, 2, 1, 1, 1, 1, 4, 2]
def baseStart_6968132 : Nat := 118140960795 + 6968132 * 2 ^ 59
def prefixEnd_6968132 : Nat := 4983230072969 + 3 ^ 40 * 6968132 * 2
def baseEnd_6968132 : Nat := 3578000979975236385204151

theorem tailTrace_6968132 : CollatzResearch.WordTrace tailWord_6968132 prefixEnd_6968132 3578000979975236385204151 := by
  unfold tailWord_6968132
  simp only [CollatzResearch.WordTrace]
  refine ⟨127074326595827650522509325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169432435461103534030012433 127074326595827650522509325)
  ·
    refine ⟨47652872473435368945940997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127074326595827650522509325 47652872473435368945940997)
    ·
      refine ⟨8934913588769131677363937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47652872473435368945940997 8934913588769131677363937)
      ·
        refine ⟨6701185191576848758022953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8934913588769131677363937 6701185191576848758022953)
        ·
          refine ⟨5025888893682636568517215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6701185191576848758022953 5025888893682636568517215)
          ·
            refine ⟨7538833340523954852775823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5025888893682636568517215 7538833340523954852775823)
            ·
              refine ⟨11308250010785932279163735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7538833340523954852775823 11308250010785932279163735)
              ·
                refine ⟨16962375016178898418745603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11308250010785932279163735 16962375016178898418745603)
                ·
                  refine ⟨25443562524268347628118405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16962375016178898418745603 25443562524268347628118405)
                  ·
                    refine ⟨4770667973300315180272201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25443562524268347628118405 4770667973300315180272201)
                    ·
                      refine ⟨3578000979975236385204151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4770667973300315180272201 3578000979975236385204151)
                      ·
                        rfl

theorem cell23_6968132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_6968132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968132 prefixEnd_6968132 := by exact prefixLift 6968132
  have htrace : WordTrace (prefixWord ++ tailWord_6968132) baseStart_6968132 baseEnd_6968132 := by
    simpa [prefixWord, tailWord_6968132, baseEnd_6968132] using wordTrace_append hprefix tailTrace_6968132
  have hstable : (prefixWord ++ tailWord_6968132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968132).length < 2 ^ (prefixWord ++ tailWord_6968132).sum := by decide
  have hdescent : baseEnd_6968132 < baseStart_6968132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968137 : List Nat := [1, 2, 1, 1, 2, 5, 1, 2, 1, 3, 4]
def baseStart_6968137 : Nat := 118140960795 + 6968137 * 2 ^ 59
def prefixEnd_6968137 : Nat := 4983230072969 + 3 ^ 40 * 6968137 * 2
def baseEnd_6968137 : Nat := 3578003547378508865641627

theorem tailTrace_6968137 : CollatzResearch.WordTrace tailWord_6968137 prefixEnd_6968137 3578003547378508865641627 := by
  unfold tailWord_6968137
  simp only [CollatzResearch.WordTrace]
  refine ⟨254148835556637186898950665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169432557037758124599300443 254148835556637186898950665)
  ·
    refine ⟨190611626667477890174212999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254148835556637186898950665 190611626667477890174212999)
    ·
      refine ⟨285917440001216835261319499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190611626667477890174212999 285917440001216835261319499)
      ·
        refine ⟨428876160001825252891979249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285917440001216835261319499 428876160001825252891979249)
        ·
          refine ⟨321657120001368939668984437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428876160001825252891979249 321657120001368939668984437)
          ·
            refine ⟨30155355000128338093967291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 321657120001368939668984437 30155355000128338093967291)
            ·
              refine ⟨45233032500192507140950937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30155355000128338093967291 45233032500192507140950937)
              ·
                refine ⟨33924774375144380355713203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45233032500192507140950937 33924774375144380355713203)
                ·
                  refine ⟨50887161562716570533569805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33924774375144380355713203 50887161562716570533569805)
                  ·
                    refine ⟨19082685586018713950088677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50887161562716570533569805 19082685586018713950088677)
                    ·
                      refine ⟨3578003547378508865641627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19082685586018713950088677 3578003547378508865641627)
                      ·
                        rfl

theorem cell23_6968137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 3, 4].length) (baseStart_6968137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968137 prefixEnd_6968137 := by exact prefixLift 6968137
  have htrace : WordTrace (prefixWord ++ tailWord_6968137) baseStart_6968137 baseEnd_6968137 := by
    simpa [prefixWord, tailWord_6968137, baseEnd_6968137] using wordTrace_append hprefix tailTrace_6968137
  have hstable : (prefixWord ++ tailWord_6968137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968137).length < 2 ^ (prefixWord ++ tailWord_6968137).sum := by decide
  have hdescent : baseEnd_6968137 < baseStart_6968137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968177 : List Nat := [1, 2, 2, 2, 1, 4, 2, 1, 8]
def baseStart_6968177 : Nat := 118140960795 + 6968177 * 2 ^ 59
def prefixEnd_6968177 : Nat := 4983230072969 + 3 ^ 40 * 6968177 * 2
def baseEnd_6968177 : Nat := 397558231844965412126827

theorem tailTrace_6968177 : CollatzResearch.WordTrace tailWord_6968177 prefixEnd_6968177 397558231844965412126827 := by
  unfold tailWord_6968177
  simp only [CollatzResearch.WordTrace]
  refine ⟨254150294476492273730406785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169433529650994849153604523 254150294476492273730406785)
  ·
    refine ⟨190612720857369205297805089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254150294476492273730406785 190612720857369205297805089)
    ·
      refine ⟨142959540643026903973353817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190612720857369205297805089 142959540643026903973353817)
      ·
        refine ⟨107219655482270177980015363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142959540643026903973353817 107219655482270177980015363)
        ·
          refine ⟨160829483223405266970023045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107219655482270177980015363 160829483223405266970023045)
          ·
            refine ⟨30155528104388487556879321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160829483223405266970023045 30155528104388487556879321)
            ·
              refine ⟨22616646078291365667659491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30155528104388487556879321 22616646078291365667659491)
              ·
                refine ⟨33924969117437048501489237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22616646078291365667659491 33924969117437048501489237)
                ·
                  refine ⟨397558231844965412126827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33924969117437048501489237 397558231844965412126827)
                  ·
                    rfl

theorem cell23_6968177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 8].length) (baseStart_6968177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968177 prefixEnd_6968177 := by exact prefixLift 6968177
  have htrace : WordTrace (prefixWord ++ tailWord_6968177) baseStart_6968177 baseEnd_6968177 := by
    simpa [prefixWord, tailWord_6968177, baseEnd_6968177] using wordTrace_append hprefix tailTrace_6968177
  have hstable : (prefixWord ++ tailWord_6968177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968177).length < 2 ^ (prefixWord ++ tailWord_6968177).sum := by decide
  have hdescent : baseEnd_6968177 < baseStart_6968177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968181 : List Nat := [1, 3, 4, 1, 1, 2, 3, 1, 3, 4]
def baseStart_6968181 : Nat := 118140960795 + 6968181 * 2 ^ 59
def prefixEnd_6968181 : Nat := 4983230072969 + 3 ^ 40 * 6968181 * 2
def baseEnd_6968181 : Nat := 1192675380175768897830475

theorem tailTrace_6968181 : CollatzResearch.WordTrace tailWord_6968181 prefixEnd_6968181 1192675380175768897830475 := by
  unfold tailWord_6968181
  simp only [CollatzResearch.WordTrace]
  refine ⟨254150440368477782413552397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169433626912318521609034931 254150440368477782413552397)
  ·
    refine ⟨95306415138179168405082149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254150440368477782413552397 95306415138179168405082149)
    ·
      refine ⟨17869952838408594075952903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95306415138179168405082149 17869952838408594075952903)
      ·
        refine ⟨26804929257612891113929355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17869952838408594075952903 26804929257612891113929355)
        ·
          refine ⟨40207393886419336670894033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26804929257612891113929355 40207393886419336670894033)
          ·
            refine ⟨30155545414814502503170525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40207393886419336670894033 30155545414814502503170525)
            ·
              refine ⟨11308329530555438438688947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30155545414814502503170525 11308329530555438438688947)
              ·
                refine ⟨16962494295833157658033421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11308329530555438438688947 16962494295833157658033421)
                ·
                  refine ⟨6360935360937434121762533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16962494295833157658033421 6360935360937434121762533)
                  ·
                    refine ⟨1192675380175768897830475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6360935360937434121762533 1192675380175768897830475)
                    ·
                      rfl

theorem cell23_6968181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_6968181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968181 prefixEnd_6968181 := by exact prefixLift 6968181
  have htrace : WordTrace (prefixWord ++ tailWord_6968181) baseStart_6968181 baseEnd_6968181 := by
    simpa [prefixWord, tailWord_6968181, baseEnd_6968181] using wordTrace_append hprefix tailTrace_6968181
  have hstable : (prefixWord ++ tailWord_6968181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968181).length < 2 ^ (prefixWord ++ tailWord_6968181).sum := by decide
  have hdescent : baseEnd_6968181 < baseStart_6968181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968224 : List Nat := [2, 1, 1, 4, 1, 1, 2, 5, 1, 5]
def baseStart_6968224 : Nat := 118140960795 + 6968224 * 2 ^ 59
def prefixEnd_6968224 : Nat := 4983230072969 + 3 ^ 40 * 6968224 * 2
def baseEnd_6968224 : Nat := 1192682740065150008417909

theorem tailTrace_6968224 : CollatzResearch.WordTrace tailWord_6968224 prefixEnd_6968224 1192682740065150008417909 := by
  unfold tailWord_6968224
  simp only [CollatzResearch.WordTrace]
  refine ⟨127076004353661000378683863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169434672471548000504911817 127076004353661000378683863)
  ·
    refine ⟨190614006530491500568025795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127076004353661000378683863 190614006530491500568025795)
    ·
      refine ⟨285921009795737250852038693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190614006530491500568025795 285921009795737250852038693)
      ·
        refine ⟨53610189336700734534757255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 285921009795737250852038693 53610189336700734534757255)
        ·
          refine ⟨80415284005051101802135883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53610189336700734534757255 80415284005051101802135883)
          ·
            refine ⟨120622926007576652703203825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80415284005051101802135883 120622926007576652703203825)
            ·
              refine ⟨90467194505682489527402869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120622926007576652703203825 90467194505682489527402869)
              ·
                refine ⟨8481299484907733393194019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90467194505682489527402869 8481299484907733393194019)
                ·
                  refine ⟨12721949227361600089791029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8481299484907733393194019 12721949227361600089791029)
                  ·
                    refine ⟨1192682740065150008417909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12721949227361600089791029 1192682740065150008417909)
                    ·
                      rfl

theorem cell23_6968224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 1, 5].length) (baseStart_6968224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968224 prefixEnd_6968224 := by exact prefixLift 6968224
  have htrace : WordTrace (prefixWord ++ tailWord_6968224) baseStart_6968224 baseEnd_6968224 := by
    simpa [prefixWord, tailWord_6968224, baseEnd_6968224] using wordTrace_append hprefix tailTrace_6968224
  have hstable : (prefixWord ++ tailWord_6968224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968224).length < 2 ^ (prefixWord ++ tailWord_6968224).sum := by decide
  have hdescent : baseEnd_6968224 < baseStart_6968224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968295 : List Nat := [1, 1, 5, 2, 2, 2, 2, 1, 3, 2, 2]
def baseStart_6968295 : Nat := 118140960795 + 6968295 * 2 ^ 59
def prefixEnd_6968295 : Nat := 4983230072969 + 3 ^ 40 * 6968295 * 2
def baseEnd_6968295 : Nat := 3578084677321919247465901

theorem tailTrace_6968295 : CollatzResearch.WordTrace tailWord_6968295 prefixEnd_6968295 3578084677321919247465901 := by
  unfold tailWord_6968295
  simp only [CollatzResearch.WordTrace]
  refine ⟨254154598290064779883202339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169436398860043186588801559 254154598290064779883202339)
  ·
    refine ⟨381231897435097169824803509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254154598290064779883202339 381231897435097169824803509)
    ·
      refine ⟨35740490384540359671075329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 381231897435097169824803509 35740490384540359671075329)
      ·
        refine ⟨26805367788405269753306497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35740490384540359671075329 26805367788405269753306497)
        ·
          refine ⟨20104025841303952314979873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26805367788405269753306497 20104025841303952314979873)
          ·
            refine ⟨15078019380977964236234905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20104025841303952314979873 15078019380977964236234905)
            ·
              refine ⟨11308514535733473177176179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15078019380977964236234905 11308514535733473177176179)
              ·
                refine ⟨16962771803600209765764269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11308514535733473177176179 16962771803600209765764269)
                ·
                  refine ⟨6361039426350078662161601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16962771803600209765764269 6361039426350078662161601)
                  ·
                    refine ⟨4770779569762558996621201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6361039426350078662161601 4770779569762558996621201)
                    ·
                      refine ⟨3578084677321919247465901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4770779569762558996621201 3578084677321919247465901)
                      ·
                        rfl

theorem cell23_6968295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_6968295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968295 prefixEnd_6968295 := by exact prefixLift 6968295
  have htrace : WordTrace (prefixWord ++ tailWord_6968295) baseStart_6968295 baseEnd_6968295 := by
    simpa [prefixWord, tailWord_6968295, baseEnd_6968295] using wordTrace_append hprefix tailTrace_6968295
  have hstable : (prefixWord ++ tailWord_6968295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968295).length < 2 ^ (prefixWord ++ tailWord_6968295).sum := by decide
  have hdescent : baseEnd_6968295 < baseStart_6968295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968364 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 4]
def baseStart_6968364 : Nat := 118140960795 + 6968364 * 2 ^ 59
def prefixEnd_6968364 : Nat := 4983230072969 + 3 ^ 40 * 6968364 * 2
def baseEnd_6968364 : Nat := 3578120107487079477503083

theorem tailTrace_6968364 : CollatzResearch.WordTrace tailWord_6968364 prefixEnd_6968364 3578120107487079477503083 := by
  unfold tailWord_6968364
  simp only [CollatzResearch.WordTrace]
  refine ⟨127078557463407402333732073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169438076617876536444976097 127078557463407402333732073)
  ·
    refine ⟨95308918097555551750299055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127078557463407402333732073 95308918097555551750299055)
    ·
      refine ⟨142963377146333327625448583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95308918097555551750299055 142963377146333327625448583)
      ·
        refine ⟨214445065719499991438172875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142963377146333327625448583 214445065719499991438172875)
        ·
          refine ⟨321667598579249987157259313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214445065719499991438172875 321667598579249987157259313)
          ·
            refine ⟨241250698934437490367944485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321667598579249987157259313 241250698934437490367944485)
            ·
              refine ⟨45234506050207029443989591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 241250698934437490367944485 45234506050207029443989591)
              ·
                refine ⟨67851759075310544165984387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45234506050207029443989591 67851759075310544165984387)
                ·
                  refine ⟨101777638612965816248976581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67851759075310544165984387 101777638612965816248976581)
                  ·
                    refine ⟨19083307239931090546683109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101777638612965816248976581 19083307239931090546683109)
                    ·
                      refine ⟨3578120107487079477503083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19083307239931090546683109 3578120107487079477503083)
                      ·
                        rfl

theorem cell23_6968364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_6968364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968364 prefixEnd_6968364 := by exact prefixLift 6968364
  have htrace : WordTrace (prefixWord ++ tailWord_6968364) baseStart_6968364 baseEnd_6968364 := by
    simpa [prefixWord, tailWord_6968364, baseEnd_6968364] using wordTrace_append hprefix tailTrace_6968364
  have hstable : (prefixWord ++ tailWord_6968364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968364).length < 2 ^ (prefixWord ++ tailWord_6968364).sum := by decide
  have hdescent : baseEnd_6968364 < baseStart_6968364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968372 : List Nat := [2, 5, 1, 2, 1, 1, 3, 2, 1, 3, 2]
def baseStart_6968372 : Nat := 118140960795 + 6968372 * 2 ^ 59
def prefixEnd_6968372 : Nat := 4983230072969 + 3 ^ 40 * 6968372 * 2
def baseEnd_6968372 : Nat := 3578124215332315446203047

theorem tailTrace_6968372 : CollatzResearch.WordTrace tailWord_6968372 prefixEnd_6968372 3578124215332315446203047 := by
  unfold tailWord_6968372
  simp only [CollatzResearch.WordTrace]
  refine ⟨127078703355392911016877685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169438271140523881355836913 127078703355392911016877685)
  ·
    refine ⟨11913628439568085407832283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127078703355392911016877685 11913628439568085407832283)
    ·
      refine ⟨17870442659352128111748425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11913628439568085407832283 17870442659352128111748425)
      ·
        refine ⟨13402831994514096083811319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17870442659352128111748425 13402831994514096083811319)
        ·
          refine ⟨20104247991771144125716979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13402831994514096083811319 20104247991771144125716979)
          ·
            refine ⟨30156371987656716188575469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20104247991771144125716979 30156371987656716188575469)
            ·
              refine ⟨11308639495371268570715801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30156371987656716188575469 11308639495371268570715801)
              ·
                refine ⟨8481479621528451428036851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11308639495371268570715801 8481479621528451428036851)
                ·
                  refine ⟨12722219432292677142055277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8481479621528451428036851 12722219432292677142055277)
                  ·
                    refine ⟨4770832287109753928270729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12722219432292677142055277 4770832287109753928270729)
                    ·
                      refine ⟨3578124215332315446203047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4770832287109753928270729 3578124215332315446203047)
                      ·
                        rfl

theorem cell23_6968372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_6968372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968372 prefixEnd_6968372 := by exact prefixLift 6968372
  have htrace : WordTrace (prefixWord ++ tailWord_6968372) baseStart_6968372 baseEnd_6968372 := by
    simpa [prefixWord, tailWord_6968372, baseEnd_6968372] using wordTrace_append hprefix tailTrace_6968372
  have hstable : (prefixWord ++ tailWord_6968372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968372).length < 2 ^ (prefixWord ++ tailWord_6968372).sum := by decide
  have hdescent : baseEnd_6968372 < baseStart_6968372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968385 : List Nat := [1, 2, 5, 1, 3, 1, 1, 2, 1, 4, 2]
def baseStart_6968385 : Nat := 118140960795 + 6968385 * 2 ^ 59
def prefixEnd_6968385 : Nat := 4983230072969 + 3 ^ 40 * 6968385 * 2
def baseEnd_6968385 : Nat := 3578130890580823895340487

theorem tailTrace_6968385 : CollatzResearch.WordTrace tailWord_6968385 prefixEnd_6968385 3578130890580823895340487 := by
  unfold tailWord_6968385
  simp only [CollatzResearch.WordTrace]
  refine ⟨254157880859738725253978609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169438587239825816835985739 254157880859738725253978609)
  ·
    refine ⟨190618410644804043940483957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254157880859738725253978609 190618410644804043940483957)
    ·
      refine ⟨17870475997950379119420371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 190618410644804043940483957 17870475997950379119420371)
      ·
        refine ⟨26805713996925568679130557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17870475997950379119420371 26805713996925568679130557)
        ·
          refine ⟨10052142748847088254673959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26805713996925568679130557 10052142748847088254673959)
          ·
            refine ⟨15078214123270632382010939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10052142748847088254673959 15078214123270632382010939)
            ·
              refine ⟨22617321184905948573016409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15078214123270632382010939 22617321184905948573016409)
              ·
                refine ⟨16962990888679461429762307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22617321184905948573016409 16962990888679461429762307)
                ·
                  refine ⟨25444486333019192144643461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16962990888679461429762307 25444486333019192144643461)
                  ·
                    refine ⟨4770841187441098527120649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25444486333019192144643461 4770841187441098527120649)
                    ·
                      refine ⟨3578130890580823895340487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4770841187441098527120649 3578130890580823895340487)
                      ·
                        rfl

theorem cell23_6968385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_6968385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968385 prefixEnd_6968385 := by exact prefixLift 6968385
  have htrace : WordTrace (prefixWord ++ tailWord_6968385) baseStart_6968385 baseEnd_6968385 := by
    simpa [prefixWord, tailWord_6968385, baseEnd_6968385] using wordTrace_append hprefix tailTrace_6968385
  have hstable : (prefixWord ++ tailWord_6968385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968385).length < 2 ^ (prefixWord ++ tailWord_6968385).sum := by decide
  have hdescent : baseEnd_6968385 < baseStart_6968385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968402 : List Nat := [3, 2, 2, 1, 3, 2, 2, 2, 2, 2, 2]
def baseStart_6968402 : Nat := 118140960795 + 6968402 * 2 ^ 59
def prefixEnd_6968402 : Nat := 4983230072969 + 3 ^ 40 * 6968402 * 2
def baseEnd_6968402 : Nat := 3578139619751950328827909

theorem tailTrace_6968402 : CollatzResearch.WordTrace tailWord_6968402 prefixEnd_6968402 3578139619751950328827909 := by
  unfold tailWord_6968402
  simp only [CollatzResearch.WordTrace]
  refine ⟨63539625225169284289336865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169439000600451424771564973 63539625225169284289336865)
  ·
    refine ⟨47654718918876963217002649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63539625225169284289336865 47654718918876963217002649)
    ·
      refine ⟨35741039189157722412751987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47654718918876963217002649 35741039189157722412751987)
      ·
        refine ⟨53611558783736583619127981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35741039189157722412751987 53611558783736583619127981)
        ·
          refine ⟨20104334543901218857172993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53611558783736583619127981 20104334543901218857172993)
          ·
            refine ⟨15078250907925914142879745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20104334543901218857172993 15078250907925914142879745)
            ·
              refine ⟨11308688180944435607159809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15078250907925914142879745 11308688180944435607159809)
              ·
                refine ⟨8481516135708326705369857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11308688180944435607159809 8481516135708326705369857)
                ·
                  refine ⟨6361137101781245029027393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8481516135708326705369857 6361137101781245029027393)
                  ·
                    refine ⟨4770852826335933771770545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6361137101781245029027393 4770852826335933771770545)
                    ·
                      refine ⟨3578139619751950328827909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4770852826335933771770545 3578139619751950328827909)
                      ·
                        rfl

theorem cell23_6968402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_6968402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968402 prefixEnd_6968402 := by exact prefixLift 6968402
  have htrace : WordTrace (prefixWord ++ tailWord_6968402) baseStart_6968402 baseEnd_6968402 := by
    simpa [prefixWord, tailWord_6968402, baseEnd_6968402] using wordTrace_append hprefix tailTrace_6968402
  have hstable : (prefixWord ++ tailWord_6968402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968402).length < 2 ^ (prefixWord ++ tailWord_6968402).sum := by decide
  have hdescent : baseEnd_6968402 < baseStart_6968402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968418 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 1, 5, 3]
def baseStart_6968418 : Nat := 118140960795 + 6968418 * 2 ^ 59
def prefixEnd_6968418 : Nat := 4983230072969 + 3 ^ 40 * 6968418 * 2
def baseEnd_6968418 : Nat := 3578147835442422266227835

theorem tailTrace_6968418 : CollatzResearch.WordTrace tailWord_6968418 prefixEnd_6968418 3578147835442422266227835 := by
  unfold tailWord_6968418
  simp only [CollatzResearch.WordTrace]
  refine ⟨63539771117154792972482477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169439389645746114593286605 63539771117154792972482477)
  ·
    refine ⟨23827414168933047364680929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63539771117154792972482477 23827414168933047364680929)
    ·
      refine ⟨17870560626699785523510697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23827414168933047364680929 17870560626699785523510697)
      ·
        refine ⟨13402920470024839142633023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17870560626699785523510697 13402920470024839142633023)
        ·
          refine ⟨20104380705037258713949535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13402920470024839142633023 20104380705037258713949535)
          ·
            refine ⟨30156571057555888070924303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20104380705037258713949535 30156571057555888070924303)
            ·
              refine ⟨45234856586333832106386455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30156571057555888070924303 45234856586333832106386455)
              ·
                refine ⟨67852284879500748159579683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45234856586333832106386455 67852284879500748159579683)
                ·
                  refine ⟨101778427319251122239369525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67852284879500748159579683 101778427319251122239369525)
                  ·
                    refine ⟨9541727561179792709940893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101778427319251122239369525 9541727561179792709940893)
                    ·
                      refine ⟨3578147835442422266227835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9541727561179792709940893 3578147835442422266227835)
                      ·
                        rfl

theorem cell23_6968418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_6968418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968418 prefixEnd_6968418 := by exact prefixLift 6968418
  have htrace : WordTrace (prefixWord ++ tailWord_6968418) baseStart_6968418 baseEnd_6968418 := by
    simpa [prefixWord, tailWord_6968418, baseEnd_6968418] using wordTrace_append hprefix tailTrace_6968418
  have hstable : (prefixWord ++ tailWord_6968418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968418).length < 2 ^ (prefixWord ++ tailWord_6968418).sum := by decide
  have hdescent : baseEnd_6968418 < baseStart_6968418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968451 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 5, 4]
def baseStart_6968451 : Nat := 118140960795 + 6968451 * 2 ^ 59
def prefixEnd_6968451 : Nat := 4983230072969 + 3 ^ 40 * 6968451 * 2
def baseEnd_6968451 : Nat := 1192721593434673545705061

theorem tailTrace_6968451 : CollatzResearch.WordTrace tailWord_6968451 prefixEnd_6968451 1192721593434673545705061 := by
  unfold tailWord_6968451
  simp only [CollatzResearch.WordTrace]
  refine ⟨254160288077499618525881207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169440192051666412350587471 254160288077499618525881207)
  ·
    refine ⟨381240432116249427788821811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254160288077499618525881207 381240432116249427788821811)
    ·
      refine ⟨571860648174374141683232717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381240432116249427788821811 571860648174374141683232717)
      ·
        refine ⟨214447743065390303131212269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 571860648174374141683232717 214447743065390303131212269)
        ·
          refine ⟨80417903649521363674204601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214447743065390303131212269 80417903649521363674204601)
          ·
            refine ⟨60313427737141022755653451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80417903649521363674204601 60313427737141022755653451)
            ·
              refine ⟨90470141605711534133480177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60313427737141022755653451 90470141605711534133480177)
              ·
                refine ⟨67852606204283650600110133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90470141605711534133480177 67852606204283650600110133)
                ·
                  refine ⟨6361181831651592243760325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67852606204283650600110133 6361181831651592243760325)
                  ·
                    refine ⟨1192721593434673545705061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6361181831651592243760325 1192721593434673545705061)
                    ·
                      rfl

theorem cell23_6968451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 5, 4].length) (baseStart_6968451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968451 prefixEnd_6968451 := by exact prefixLift 6968451
  have htrace : WordTrace (prefixWord ++ tailWord_6968451) baseStart_6968451 baseEnd_6968451 := by
    simpa [prefixWord, tailWord_6968451, baseEnd_6968451] using wordTrace_append hprefix tailTrace_6968451
  have hstable : (prefixWord ++ tailWord_6968451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968451).length < 2 ^ (prefixWord ++ tailWord_6968451).sum := by decide
  have hdescent : baseEnd_6968451 < baseStart_6968451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968458 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 4, 4, 2]
def baseStart_6968458 : Nat := 118140960795 + 6968458 * 2 ^ 59
def prefixEnd_6968458 : Nat := 4983230072969 + 3 ^ 40 * 6968458 * 2
def baseEnd_6968458 : Nat := 3578168374668602109727651

theorem tailTrace_6968458 : CollatzResearch.WordTrace tailWord_6968458 prefixEnd_6968458 3578168374668602109727651 := by
  unfold tailWord_6968458
  simp only [CollatzResearch.WordTrace]
  refine ⟨63540135847118564680346507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169440362258982839147590685 63540135847118564680346507)
  ·
    refine ⟨95310203770677847020519761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63540135847118564680346507 95310203770677847020519761)
    ·
      refine ⟨71482652828008385265389821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95310203770677847020519761 71482652828008385265389821)
      ·
        refine ⟨26805994810503144474521183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71482652828008385265389821 26805994810503144474521183)
        ·
          refine ⟨40208992215754716711781775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26805994810503144474521183 40208992215754716711781775)
          ·
            refine ⟨60313488323632075067672663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40208992215754716711781775 60313488323632075067672663)
            ·
              refine ⟨90470232485448112601508995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60313488323632075067672663 90470232485448112601508995)
              ·
                refine ⟨135705348728172168902263493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90470232485448112601508995 135705348728172168902263493)
                ·
                  refine ⟨25444752886532281669174405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135705348728172168902263493 25444752886532281669174405)
                  ·
                    refine ⟨4770891166224802812970201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25444752886532281669174405 4770891166224802812970201)
                    ·
                      refine ⟨3578168374668602109727651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4770891166224802812970201 3578168374668602109727651)
                      ·
                        rfl

theorem cell23_6968458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_6968458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968458 prefixEnd_6968458 := by exact prefixLift 6968458
  have htrace : WordTrace (prefixWord ++ tailWord_6968458) baseStart_6968458 baseEnd_6968458 := by
    simpa [prefixWord, tailWord_6968458, baseEnd_6968458] using wordTrace_append hprefix tailTrace_6968458
  have hstable : (prefixWord ++ tailWord_6968458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968458).length < 2 ^ (prefixWord ++ tailWord_6968458).sum := by decide
  have hdescent : baseEnd_6968458 < baseStart_6968458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968531 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 4]
def baseStart_6968531 : Nat := 118140960795 + 6968531 * 2 ^ 59
def prefixEnd_6968531 : Nat := 4983230072969 + 3 ^ 40 * 6968531 * 2
def baseEnd_6968531 : Nat := 3578205858756380324114815

theorem tailTrace_6968531 : CollatzResearch.WordTrace tailWord_6968531 prefixEnd_6968531 3578205858756380324114815 := by
  unfold tailWord_6968531
  simp only [CollatzResearch.WordTrace]
  refine ⟨254163205917209792188793447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169442137278139861459195631 254163205917209792188793447)
  ·
    refine ⟨381244808875814688283190171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254163205917209792188793447 381244808875814688283190171)
    ·
      refine ⟨571867213313722032424785257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381244808875814688283190171 571867213313722032424785257)
      ·
        refine ⟨428900409985291524318588943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 571867213313722032424785257 428900409985291524318588943)
        ·
          refine ⟨643350614977937286477883415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428900409985291524318588943 643350614977937286477883415)
          ·
            refine ⟨965025922466905929716825123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643350614977937286477883415 965025922466905929716825123)
            ·
              refine ⟨1447538883700358894575237685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965025922466905929716825123 1447538883700358894575237685)
              ·
                refine ⟨135706770346908646366428533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1447538883700358894575237685 135706770346908646366428533)
                ·
                  refine ⟨12722509720022685596852675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135706770346908646366428533 12722509720022685596852675)
                  ·
                    refine ⟨19083764580034028395279013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12722509720022685596852675 19083764580034028395279013)
                    ·
                      refine ⟨3578205858756380324114815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19083764580034028395279013 3578205858756380324114815)
                      ·
                        rfl

theorem cell23_6968531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 4].length) (baseStart_6968531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968531 prefixEnd_6968531 := by exact prefixLift 6968531
  have htrace : WordTrace (prefixWord ++ tailWord_6968531) baseStart_6968531 baseEnd_6968531 := by
    simpa [prefixWord, tailWord_6968531, baseEnd_6968531] using wordTrace_append hprefix tailTrace_6968531
  have hstable : (prefixWord ++ tailWord_6968531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968531).length < 2 ^ (prefixWord ++ tailWord_6968531).sum := by decide
  have hdescent : baseEnd_6968531 < baseStart_6968531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968545 : List Nat := [1, 2, 3, 1, 3, 4, 1, 2, 1, 5]
def baseStart_6968545 : Nat := 118140960795 + 6968545 * 2 ^ 59
def prefixEnd_6968545 : Nat := 4983230072969 + 3 ^ 40 * 6968545 * 2
def baseEnd_6968545 : Nat := 1192737682495181089779917

theorem tailTrace_6968545 : CollatzResearch.WordTrace tailWord_6968545 prefixEnd_6968545 1192737682495181089779917 := by
  unfold tailWord_6968545
  simp only [CollatzResearch.WordTrace]
  refine ⟨254163716539159072579803089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169442477692772715053202059 254163716539159072579803089)
  ·
    refine ⟨190622787404369304434852317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254163716539159072579803089 190622787404369304434852317)
    ·
      refine ⟨71483545276638489163069619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190622787404369304434852317 71483545276638489163069619)
      ·
        refine ⟨107225317914957733744604429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71483545276638489163069619 107225317914957733744604429)
        ·
          refine ⟨40209494218109150154226661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107225317914957733744604429 40209494218109150154226661)
          ·
            refine ⟨7539280165895465653917499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40209494218109150154226661 7539280165895465653917499)
            ·
              refine ⟨11308920248843198480876249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7539280165895465653917499 11308920248843198480876249)
              ·
                refine ⟨8481690186632398860657187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11308920248843198480876249 8481690186632398860657187)
                ·
                  refine ⟨12722535279948598290985781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8481690186632398860657187 12722535279948598290985781)
                  ·
                    refine ⟨1192737682495181089779917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12722535279948598290985781 1192737682495181089779917)
                    ·
                      rfl

theorem cell23_6968545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_6968545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968545 prefixEnd_6968545 := by exact prefixLift 6968545
  have htrace : WordTrace (prefixWord ++ tailWord_6968545) baseStart_6968545 baseEnd_6968545 := by
    simpa [prefixWord, tailWord_6968545, baseEnd_6968545] using wordTrace_append hprefix tailTrace_6968545
  have hstable : (prefixWord ++ tailWord_6968545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968545).length < 2 ^ (prefixWord ++ tailWord_6968545).sum := by decide
  have hdescent : baseEnd_6968545 < baseStart_6968545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968548 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 2, 6, 2]
def baseStart_6968548 : Nat := 118140960795 + 6968548 * 2 ^ 59
def prefixEnd_6968548 : Nat := 4983230072969 + 3 ^ 40 * 6968548 * 2
def baseEnd_6968548 : Nat := 3578214587927506757602237

theorem tailTrace_6968548 : CollatzResearch.WordTrace tailWord_6968548 prefixEnd_6968548 3578214587927506757602237 := by
  unfold tailWord_6968548
  simp only [CollatzResearch.WordTrace]
  refine ⟨127081912979074102046081149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169442550638765469394774865 127081912979074102046081149)
  ·
    refine ⟨47655717367152788267280431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127081912979074102046081149 47655717367152788267280431)
    ·
      refine ⟨71483576050729182400920647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47655717367152788267280431 71483576050729182400920647)
      ·
        refine ⟨107225364076093773601380971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71483576050729182400920647 107225364076093773601380971)
        ·
          refine ⟨160838046114140660402071457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107225364076093773601380971 160838046114140660402071457)
          ·
            refine ⟨120628534585605495301553593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160838046114140660402071457 120628534585605495301553593)
            ·
              refine ⟨90471400939204121476165195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120628534585605495301553593 90471400939204121476165195)
              ·
                refine ⟨135707101408806182214247793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90471400939204121476165195 135707101408806182214247793)
                ·
                  refine ⟨101780326056604636660685845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135707101408806182214247793 101780326056604636660685845)
                  ·
                    refine ⟨4770952783903342343469649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101780326056604636660685845 4770952783903342343469649)
                    ·
                      refine ⟨3578214587927506757602237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4770952783903342343469649 3578214587927506757602237)
                      ·
                        rfl

theorem cell23_6968548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 2, 6, 2].length) (baseStart_6968548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968548 prefixEnd_6968548 := by exact prefixLift 6968548
  have htrace : WordTrace (prefixWord ++ tailWord_6968548) baseStart_6968548 baseEnd_6968548 := by
    simpa [prefixWord, tailWord_6968548, baseEnd_6968548] using wordTrace_append hprefix tailTrace_6968548
  have hstable : (prefixWord ++ tailWord_6968548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968548).length < 2 ^ (prefixWord ++ tailWord_6968548).sum := by decide
  have hdescent : baseEnd_6968548 < baseStart_6968548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968558 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 6, 4]
def baseStart_6968558 : Nat := 118140960795 + 6968558 * 2 ^ 59
def prefixEnd_6968558 : Nat := 4983230072969 + 3 ^ 40 * 6968558 * 2
def baseEnd_6968558 : Nat := 1192739907578017239492397

theorem tailTrace_6968558 : CollatzResearch.WordTrace tailWord_6968558 prefixEnd_6968558 1192739907578017239492397 := by
  unfold tailWord_6968558
  simp only [CollatzResearch.WordTrace]
  refine ⟨31770523836013996975003291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169442793792074650533350885 31770523836013996975003291)
  ·
    refine ⟨47655785754020995462504937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31770523836013996975003291 47655785754020995462504937)
    ·
      refine ⟨35741839315515746596878703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47655785754020995462504937 35741839315515746596878703)
      ·
        refine ⟨53612758973273619895318055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35741839315515746596878703 53612758973273619895318055)
        ·
          refine ⟨80419138459910429842977083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53612758973273619895318055 80419138459910429842977083)
          ·
            refine ⟨120628707689865644764465625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80419138459910429842977083 120628707689865644764465625)
            ·
              refine ⟨90471530767399233573349219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120628707689865644764465625 90471530767399233573349219)
              ·
                refine ⟨135707296151098850360023829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90471530767399233573349219 135707296151098850360023829)
                ·
                  refine ⟨6361279507082758610626117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135707296151098850360023829 6361279507082758610626117)
                  ·
                    refine ⟨1192739907578017239492397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6361279507082758610626117 1192739907578017239492397)
                    ·
                      rfl

theorem cell23_6968558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_6968558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968558 prefixEnd_6968558 := by exact prefixLift 6968558
  have htrace : WordTrace (prefixWord ++ tailWord_6968558) baseStart_6968558 baseEnd_6968558 := by
    simpa [prefixWord, tailWord_6968558, baseEnd_6968558] using wordTrace_append hprefix tailTrace_6968558
  have hstable : (prefixWord ++ tailWord_6968558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968558).length < 2 ^ (prefixWord ++ tailWord_6968558).sum := by decide
  have hdescent : baseEnd_6968558 < baseStart_6968558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968562 : List Nat := [3, 2, 1, 3, 3, 1, 3, 1, 1, 5]
def baseStart_6968562 : Nat := 118140960795 + 6968562 * 2 ^ 59
def prefixEnd_6968562 : Nat := 4983230072969 + 3 ^ 40 * 6968562 * 2
def baseEnd_6968562 : Nat := 1192740592218889900942391

theorem tailTrace_6968562 : CollatzResearch.WordTrace tailWord_6968562 prefixEnd_6968562 1192740592218889900942391 := by
  unfold tailWord_6968562
  simp only [CollatzResearch.WordTrace]
  refine ⟨63541084145024371120792985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169442891053398322988781293 63541084145024371120792985)
  ·
    refine ⟨47655813108768278340594739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63541084145024371120792985 47655813108768278340594739)
    ·
      refine ⟨71483719663152417510892109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47655813108768278340594739 71483719663152417510892109)
      ·
        refine ⟨26806394873682156566584541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71483719663152417510892109 26806394873682156566584541)
        ·
          refine ⟨10052398077630808712469203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26806394873682156566584541 10052398077630808712469203)
          ·
            refine ⟨15078597116446213068703805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10052398077630808712469203 15078597116446213068703805)
            ·
              refine ⟨5654473918667329900763927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15078597116446213068703805 5654473918667329900763927)
              ·
                refine ⟨8481710878000994851145891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5654473918667329900763927 8481710878000994851145891)
                ·
                  refine ⟨12722566317001492276718837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8481710878000994851145891 12722566317001492276718837)
                  ·
                    refine ⟨1192740592218889900942391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12722566317001492276718837 1192740592218889900942391)
                    ·
                      rfl

theorem cell23_6968562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_6968562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968562 prefixEnd_6968562 := by exact prefixLift 6968562
  have htrace : WordTrace (prefixWord ++ tailWord_6968562) baseStart_6968562 baseEnd_6968562 := by
    simpa [prefixWord, tailWord_6968562, baseEnd_6968562] using wordTrace_append hprefix tailTrace_6968562
  have hstable : (prefixWord ++ tailWord_6968562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968562).length < 2 ^ (prefixWord ++ tailWord_6968562).sum := by decide
  have hdescent : baseEnd_6968562 < baseStart_6968562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968575 : List Nat := [1, 1, 2, 2, 1, 6, 2, 2, 2, 4]
def baseStart_6968575 : Nat := 118140960795 + 6968575 * 2 ^ 59
def prefixEnd_6968575 : Nat := 4983230072969 + 3 ^ 40 * 6968575 * 2
def baseEnd_6968575 : Nat := 1192742817301726050654871

theorem tailTrace_6968575 : CollatzResearch.WordTrace tailWord_6968575 prefixEnd_6968575 1192742817301726050654871 := by
  unfold tailWord_6968575
  simp only [CollatzResearch.WordTrace]
  refine ⟨254164810729050387703395179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169443207152700258468930119 254164810729050387703395179)
  ·
    refine ⟨381247216093575581555092769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254164810729050387703395179 381247216093575581555092769)
    ·
      refine ⟨285935412070181686166319577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381247216093575581555092769 285935412070181686166319577)
      ·
        refine ⟨214451559052636264624739683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285935412070181686166319577 214451559052636264624739683)
        ·
          refine ⟨321677338578954396937109525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214451559052636264624739683 321677338578954396937109525)
          ·
            refine ⟨15078625245888487356427009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 321677338578954396937109525 15078625245888487356427009)
            ·
              refine ⟨11308968934416365517320257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15078625245888487356427009 11308968934416365517320257)
              ·
                refine ⟨8481726700812274137990193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11308968934416365517320257 8481726700812274137990193)
                ·
                  refine ⟨6361295025609205603492645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8481726700812274137990193 6361295025609205603492645)
                  ·
                    refine ⟨1192742817301726050654871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6361295025609205603492645 1192742817301726050654871)
                    ·
                      rfl

theorem cell23_6968575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 2, 4].length) (baseStart_6968575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968575 prefixEnd_6968575 := by exact prefixLift 6968575
  have htrace : WordTrace (prefixWord ++ tailWord_6968575) baseStart_6968575 baseEnd_6968575 := by
    simpa [prefixWord, tailWord_6968575, baseEnd_6968575] using wordTrace_append hprefix tailTrace_6968575
  have hstable : (prefixWord ++ tailWord_6968575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968575).length < 2 ^ (prefixWord ++ tailWord_6968575).sum := by decide
  have hdescent : baseEnd_6968575 < baseStart_6968575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968588 : List Nat := [2, 2, 1, 2, 2, 5, 1, 8]
def baseStart_6968588 : Nat := 118140960795 + 6968588 * 2 ^ 59
def prefixEnd_6968588 : Nat := 4983230072969 + 3 ^ 40 * 6968588 * 2
def baseEnd_6968588 : Nat := 132527226931618022263039

theorem tailTrace_6968588 : CollatzResearch.WordTrace tailWord_6968588 prefixEnd_6968588 132527226931618022263039 := by
  unfold tailWord_6968588
  simp only [CollatzResearch.WordTrace]
  refine ⟨127082642439001645461809209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169443523252002193949078945 127082642439001645461809209)
  ·
    refine ⟨95311981829251234096356907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127082642439001645461809209 95311981829251234096356907)
    ·
      refine ⟨142967972743876851144535361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95311981829251234096356907 142967972743876851144535361)
      ·
        refine ⟨107225979557907638358401521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142967972743876851144535361 107225979557907638358401521)
        ·
          refine ⟨80419484668430728768801141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107225979557907638358401521 80419484668430728768801141)
          ·
            refine ⟨7539326687665380822075107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80419484668430728768801141 7539326687665380822075107)
            ·
              refine ⟨11308990031498071233112661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7539326687665380822075107 11308990031498071233112661)
              ·
                refine ⟨132527226931618022263039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11308990031498071233112661 132527226931618022263039)
                ·
                  rfl

theorem cell23_6968588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 8].length) (baseStart_6968588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968588 prefixEnd_6968588 := by exact prefixLift 6968588
  have htrace : WordTrace (prefixWord ++ tailWord_6968588) baseStart_6968588 baseEnd_6968588 := by
    simpa [prefixWord, tailWord_6968588, baseEnd_6968588] using wordTrace_append hprefix tailTrace_6968588
  have hstable : (prefixWord ++ tailWord_6968588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968588).length < 2 ^ (prefixWord ++ tailWord_6968588).sum := by decide
  have hdescent : baseEnd_6968588 < baseStart_6968588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968605 : List Nat := [1, 4, 2, 3, 1, 2, 3, 7]
def baseStart_6968605 : Nat := 118140960795 + 6968605 * 2 ^ 59
def prefixEnd_6968605 : Nat := 4983230072969 + 3 ^ 40 * 6968605 * 2
def baseEnd_6968605 : Nat := 132527550234252334614425

theorem tailTrace_6968605 : CollatzResearch.WordTrace tailWord_6968605 prefixEnd_6968605 132527550234252334614425 := by
  unfold tailWord_6968605
  simp only [CollatzResearch.WordTrace]
  refine ⟨254165904918941702826987269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169443936612627801884658179 254165904918941702826987269)
  ·
    refine ⟨47656107172301569280060113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254165904918941702826987269 47656107172301569280060113)
    ·
      refine ⟨35742080379226176960045085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47656107172301569280060113 35742080379226176960045085)
      ·
        refine ⟨13403280142209816360016907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35742080379226176960045085 13403280142209816360016907)
        ·
          refine ⟨20104920213314724540025361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13403280142209816360016907 20104920213314724540025361)
          ·
            refine ⟨15078690159986043405019021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20104920213314724540025361 15078690159986043405019021)
            ·
              refine ⟨5654508809994766276882133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15078690159986043405019021 5654508809994766276882133)
              ·
                refine ⟨132527550234252334614425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5654508809994766276882133 132527550234252334614425)
                ·
                  rfl

theorem cell23_6968605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 7].length) (baseStart_6968605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968605 prefixEnd_6968605 := by exact prefixLift 6968605
  have htrace : WordTrace (prefixWord ++ tailWord_6968605) baseStart_6968605 baseEnd_6968605 := by
    simpa [prefixWord, tailWord_6968605, baseEnd_6968605] using wordTrace_append hprefix tailTrace_6968605
  have hstable : (prefixWord ++ tailWord_6968605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968605).length < 2 ^ (prefixWord ++ tailWord_6968605).sum := by decide
  have hdescent : baseEnd_6968605 < baseStart_6968605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968616 : List Nat := [2, 1, 5, 1, 2, 2, 2, 3, 1, 2, 2]
def baseStart_6968616 : Nat := 118140960795 + 6968616 * 2 ^ 59
def prefixEnd_6968616 : Nat := 4983230072969 + 3 ^ 40 * 6968616 * 2
def baseEnd_6968616 : Nat := 3578249504612012491551925

theorem tailTrace_6968616 : CollatzResearch.WordTrace tailWord_6968616 prefixEnd_6968616 3578249504612012491551925 := by
  unfold tailWord_6968616
  simp only [CollatzResearch.WordTrace]
  refine ⟨127083153060950925852818851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169444204081267901137091801 127083153060950925852818851)
  ·
    refine ⟨190624729591426388779228277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127083153060950925852818851 190624729591426388779228277)
    ·
      refine ⟨17871068399196223948052651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 190624729591426388779228277 17871068399196223948052651)
      ·
        refine ⟨26806602598794335922078977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17871068399196223948052651 26806602598794335922078977)
        ·
          refine ⟨20104951949095751941559233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26806602598794335922078977 20104951949095751941559233)
          ·
            refine ⟨15078713961821813956169425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20104951949095751941559233 15078713961821813956169425)
            ·
              refine ⟨11309035471366360467127069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15078713961821813956169425 11309035471366360467127069)
              ·
                refine ⟨4240888301762385175172651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11309035471366360467127069 4240888301762385175172651)
                ·
                  refine ⟨6361332452643577762758977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4240888301762385175172651 6361332452643577762758977)
                  ·
                    refine ⟨4770999339482683322069233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6361332452643577762758977 4770999339482683322069233)
                    ·
                      refine ⟨3578249504612012491551925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4770999339482683322069233 3578249504612012491551925)
                      ·
                        rfl

theorem cell23_6968616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_6968616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968616 prefixEnd_6968616 := by exact prefixLift 6968616
  have htrace : WordTrace (prefixWord ++ tailWord_6968616) baseStart_6968616 baseEnd_6968616 := by
    simpa [prefixWord, tailWord_6968616, baseEnd_6968616] using wordTrace_append hprefix tailTrace_6968616
  have hstable : (prefixWord ++ tailWord_6968616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968616).length < 2 ^ (prefixWord ++ tailWord_6968616).sum := by decide
  have hdescent : baseEnd_6968616 < baseStart_6968616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968646 : List Nat := [6, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4]
def baseStart_6968646 : Nat := 118140960795 + 6968646 * 2 ^ 59
def prefixEnd_6968646 : Nat := 4983230072969 + 3 ^ 40 * 6968646 * 2
def baseEnd_6968646 : Nat := 3578264909031647374176787

theorem tailTrace_6968646 : CollatzResearch.WordTrace tailWord_6968646 prefixEnd_6968646 3578264909031647374176787 := by
  unfold tailWord_6968646
  simp only [CollatzResearch.WordTrace]
  refine ⟨7942731259743536463413431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 169444933541195444552819861 7942731259743536463413431)
  ·
    refine ⟨11914096889615304695120147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7942731259743536463413431 11914096889615304695120147)
    ·
      refine ⟨17871145334422957042680221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11914096889615304695120147 17871145334422957042680221)
      ·
        refine ⟨6701679500408608891005083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17871145334422957042680221 6701679500408608891005083)
        ·
          refine ⟨10052519250612913336507625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6701679500408608891005083 10052519250612913336507625)
          ·
            refine ⟨7539389437959685002380719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10052519250612913336507625 7539389437959685002380719)
            ·
              refine ⟨11309084156939527503571079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7539389437959685002380719 11309084156939527503571079)
              ·
                refine ⟨16963626235409291255356619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11309084156939527503571079 16963626235409291255356619)
                ·
                  refine ⟨25445439353113936883034929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16963626235409291255356619 25445439353113936883034929)
                  ·
                    refine ⟨19084079514835452662276197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25445439353113936883034929 19084079514835452662276197)
                    ·
                      refine ⟨3578264909031647374176787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19084079514835452662276197 3578264909031647374176787)
                      ·
                        rfl

theorem cell23_6968646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_6968646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968646 prefixEnd_6968646 := by exact prefixLift 6968646
  have htrace : WordTrace (prefixWord ++ tailWord_6968646) baseStart_6968646 baseEnd_6968646 := by
    simpa [prefixWord, tailWord_6968646, baseEnd_6968646] using wordTrace_append hprefix tailTrace_6968646
  have hstable : (prefixWord ++ tailWord_6968646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968646).length < 2 ^ (prefixWord ++ tailWord_6968646).sum := by decide
  have hdescent : baseEnd_6968646 < baseStart_6968646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968658 : List Nat := [3, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5]
def baseStart_6968658 : Nat := 118140960795 + 6968658 * 2 ^ 59
def prefixEnd_6968658 : Nat := 4983230072969 + 3 ^ 40 * 6968658 * 2
def baseEnd_6968658 : Nat := 3578271070799501327226731

theorem tailTrace_6968658 : CollatzResearch.WordTrace tailWord_6968658 prefixEnd_6968658 3578271070799501327226731 := by
  unfold tailWord_6968658
  simp only [CollatzResearch.WordTrace]
  refine ⟨63541959496937423219666657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169445225325166461919111085 63541959496937423219666657)
  ·
    refine ⟨47656469622703067414749993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63541959496937423219666657 47656469622703067414749993)
    ·
      refine ⟨35742352217027300561062495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47656469622703067414749993 35742352217027300561062495)
      ·
        refine ⟨53613528325540950841593743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35742352217027300561062495 53613528325540950841593743)
        ·
          refine ⟨80420292488311426262390615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53613528325540950841593743 80420292488311426262390615)
          ·
            refine ⟨120630438732467139393585923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80420292488311426262390615 120630438732467139393585923)
            ·
              refine ⟨180945658098700709090378885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120630438732467139393585923 180945658098700709090378885)
              ·
                refine ⟨33927310893506382954446041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180945658098700709090378885 33927310893506382954446041)
                ·
                  refine ⟨25445483170129787215834531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33927310893506382954446041 25445483170129787215834531)
                  ·
                    refine ⟨38168224755194680823751797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25445483170129787215834531 38168224755194680823751797)
                    ·
                      refine ⟨3578271070799501327226731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38168224755194680823751797 3578271070799501327226731)
                      ·
                        rfl

theorem cell23_6968658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_6968658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968658 prefixEnd_6968658 := by exact prefixLift 6968658
  have htrace : WordTrace (prefixWord ++ tailWord_6968658) baseStart_6968658 baseEnd_6968658 := by
    simpa [prefixWord, tailWord_6968658, baseEnd_6968658] using wordTrace_append hprefix tailTrace_6968658
  have hstable : (prefixWord ++ tailWord_6968658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968658).length < 2 ^ (prefixWord ++ tailWord_6968658).sum := by decide
  have hdescent : baseEnd_6968658 < baseStart_6968658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968672 : List Nat := [2, 1, 1, 3, 4, 1, 1, 2, 4, 2, 2]
def baseStart_6968672 : Nat := 118140960795 + 6968672 * 2 ^ 59
def prefixEnd_6968672 : Nat := 4983230072969 + 3 ^ 40 * 6968672 * 2
def baseEnd_6968672 : Nat := 3578278259528664272451667

theorem tailTrace_6968672 : CollatzResearch.WordTrace tailWord_6968672 prefixEnd_6968672 3578278259528664272451667 := by
  unfold tailWord_6968672
  simp only [CollatzResearch.WordTrace]
  refine ⟨127084174304849486634838135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169445565739799315513117513 127084174304849486634838135)
  ·
    refine ⟨190626261457274229952257203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127084174304849486634838135 190626261457274229952257203)
    ·
      refine ⟨285939392185911344928385805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190626261457274229952257203 285939392185911344928385805)
      ·
        refine ⟨107227272069716754348144677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285939392185911344928385805 107227272069716754348144677)
        ·
          refine ⟨20105113513071891440277127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107227272069716754348144677 20105113513071891440277127)
          ·
            refine ⟨30157670269607837160415691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20105113513071891440277127 30157670269607837160415691)
            ·
              refine ⟨45236505404411755740623537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30157670269607837160415691 45236505404411755740623537)
              ·
                refine ⟨33927379053308816805467653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45236505404411755740623537 33927379053308816805467653)
                ·
                  refine ⟨6361383572495403151025185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33927379053308816805467653 6361383572495403151025185)
                  ·
                    refine ⟨4771037679371552363268889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6361383572495403151025185 4771037679371552363268889)
                    ·
                      refine ⟨3578278259528664272451667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4771037679371552363268889 3578278259528664272451667)
                      ·
                        rfl

theorem cell23_6968672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 4, 2, 2].length) (baseStart_6968672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968672 prefixEnd_6968672 := by exact prefixLift 6968672
  have htrace : WordTrace (prefixWord ++ tailWord_6968672) baseStart_6968672 baseEnd_6968672 := by
    simpa [prefixWord, tailWord_6968672, baseEnd_6968672] using wordTrace_append hprefix tailTrace_6968672
  have hstable : (prefixWord ++ tailWord_6968672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968672).length < 2 ^ (prefixWord ++ tailWord_6968672).sum := by decide
  have hdescent : baseEnd_6968672 < baseStart_6968672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968765 : List Nat := [1, 4, 1, 2, 2, 1, 2, 2, 1, 4, 3]
def baseStart_6968765 : Nat := 118140960795 + 6968765 * 2 ^ 59
def prefixEnd_6968765 : Nat := 4983230072969 + 3 ^ 40 * 6968765 * 2
def baseEnd_6968765 : Nat := 3578326013229532408588739

theorem tailTrace_6968765 : CollatzResearch.WordTrace tailWord_6968765 prefixEnd_6968765 3578326013229532408588739 := by
  unfold tailWord_6968765
  simp only [CollatzResearch.WordTrace]
  refine ⟨254171740598362050152811749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169447827065574700101874499 254171740598362050152811749)
  ·
    refine ⟨47657201362192884403652203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254171740598362050152811749 47657201362192884403652203)
    ·
      refine ⟨71485802043289326605478305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47657201362192884403652203 71485802043289326605478305)
      ·
        refine ⟨53614351532466994954108729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71485802043289326605478305 53614351532466994954108729)
        ·
          refine ⟨40210763649350246215581547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53614351532466994954108729 40210763649350246215581547)
          ·
            refine ⟨60316145474025369323372321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40210763649350246215581547 60316145474025369323372321)
            ·
              refine ⟨45237109105519026992529241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60316145474025369323372321 45237109105519026992529241)
              ·
                refine ⟨33927831829139270244396931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45237109105519026992529241 33927831829139270244396931)
                ·
                  refine ⟨50891747743708905366595397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33927831829139270244396931 50891747743708905366595397)
                  ·
                    refine ⟨9542202701945419756236637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50891747743708905366595397 9542202701945419756236637)
                    ·
                      refine ⟨3578326013229532408588739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9542202701945419756236637 3578326013229532408588739)
                      ·
                        rfl

theorem cell23_6968765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_6968765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968765 prefixEnd_6968765 := by exact prefixLift 6968765
  have htrace : WordTrace (prefixWord ++ tailWord_6968765) baseStart_6968765 baseEnd_6968765 := by
    simpa [prefixWord, tailWord_6968765, baseEnd_6968765] using wordTrace_append hprefix tailTrace_6968765
  have hstable : (prefixWord ++ tailWord_6968765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968765).length < 2 ^ (prefixWord ++ tailWord_6968765).sum := by decide
  have hdescent : baseEnd_6968765 < baseStart_6968765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968772 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 5, 4]
def baseStart_6968772 : Nat := 118140960795 + 6968772 * 2 ^ 59
def prefixEnd_6968772 : Nat := 4983230072969 + 3 ^ 40 * 6968772 * 2
def baseEnd_6968772 : Nat := 1192776535864704627067069

theorem tailTrace_6968772 : CollatzResearch.WordTrace tailWord_6968772 prefixEnd_6968772 1192776535864704627067069 := by
  unfold tailWord_6968772
  simp only [CollatzResearch.WordTrace]
  refine ⟨127085997954668345174158285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169447997272891126898877713 127085997954668345174158285)
  ·
    refine ⟨47657249233000629440309357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127085997954668345174158285 47657249233000629440309357)
    ·
      refine ⟨17871468462375236040116009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47657249233000629440309357 17871468462375236040116009)
      ·
        refine ⟨13403601346781427030087007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17871468462375236040116009 13403601346781427030087007)
        ·
          refine ⟨20105402020172140545130511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13403601346781427030087007 20105402020172140545130511)
          ·
            refine ⟨30158103030258210817695767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20105402020172140545130511 30158103030258210817695767)
            ·
              refine ⟨45237154545387316226543651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30158103030258210817695767 45237154545387316226543651)
              ·
                refine ⟨67855731818080974339815477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45237154545387316226543651 67855731818080974339815477)
                ·
                  refine ⟨6361474857945091344357701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67855731818080974339815477 6361474857945091344357701)
                  ·
                    refine ⟨1192776535864704627067069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6361474857945091344357701 1192776535864704627067069)
                    ·
                      rfl

theorem cell23_6968772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_6968772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968772 prefixEnd_6968772 := by exact prefixLift 6968772
  have htrace : WordTrace (prefixWord ++ tailWord_6968772) baseStart_6968772 baseEnd_6968772 := by
    simpa [prefixWord, tailWord_6968772, baseEnd_6968772] using wordTrace_append hprefix tailTrace_6968772
  have hstable : (prefixWord ++ tailWord_6968772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968772).length < 2 ^ (prefixWord ++ tailWord_6968772).sum := by decide
  have hdescent : baseEnd_6968772 < baseStart_6968772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968782 : List Nat := [4, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3]
def baseStart_6968782 : Nat := 118140960795 + 6968782 * 2 ^ 59
def prefixEnd_6968782 : Nat := 4983230072969 + 3 ^ 40 * 6968782 * 2
def baseEnd_6968782 : Nat := 3578334742400658842076161

theorem tailTrace_6968782 : CollatzResearch.WordTrace tailWord_6968782 prefixEnd_6968782 3578334742400658842076161 := by
  unfold tailWord_6968782
  simp only [CollatzResearch.WordTrace]
  refine ⟨31771545079912557757022575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169448240426200308037453733 31771545079912557757022575)
  ·
    refine ⟨47657317619868836635533863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31771545079912557757022575 47657317619868836635533863)
    ·
      refine ⟨71485976429803254953300795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47657317619868836635533863 71485976429803254953300795)
      ·
        refine ⟨107228964644704882429951193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71485976429803254953300795 107228964644704882429951193)
        ·
          refine ⟨80421723483528661822463395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107228964644704882429951193 80421723483528661822463395)
          ·
            refine ⟨120632585225292992733695093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80421723483528661822463395 120632585225292992733695093)
            ·
              refine ⟨11309304864871218068783915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120632585225292992733695093 11309304864871218068783915)
              ·
                refine ⟨16963957297306827103175873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11309304864871218068783915 16963957297306827103175873)
                ·
                  refine ⟨12722967972980120327381905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16963957297306827103175873 12722967972980120327381905)
                  ·
                    refine ⟨9542225979735090245536429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12722967972980120327381905 9542225979735090245536429)
                    ·
                      refine ⟨3578334742400658842076161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9542225979735090245536429 3578334742400658842076161)
                      ·
                        rfl

theorem cell23_6968782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_6968782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968782 prefixEnd_6968782 := by exact prefixLift 6968782
  have htrace : WordTrace (prefixWord ++ tailWord_6968782) baseStart_6968782 baseEnd_6968782 := by
    simpa [prefixWord, tailWord_6968782, baseEnd_6968782] using wordTrace_append hprefix tailTrace_6968782
  have hstable : (prefixWord ++ tailWord_6968782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968782).length < 2 ^ (prefixWord ++ tailWord_6968782).sum := by decide
  have hdescent : baseEnd_6968782 < baseStart_6968782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968789 : List Nat := [1, 3, 2, 3, 1, 1, 4, 3, 1, 4]
def baseStart_6968789 : Nat := 118140960795 + 6968789 * 2 ^ 59
def prefixEnd_6968789 : Nat := 4983230072969 + 3 ^ 40 * 6968789 * 2
def baseEnd_6968789 : Nat := 1192779445588413438229543

theorem tailTrace_6968789 : CollatzResearch.WordTrace tailWord_6968789 prefixEnd_6968789 1192779445588413438229543 := by
  unfold tailWord_6968789
  simp only [CollatzResearch.WordTrace]
  refine ⟨254172615950275102251685421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169448410633516734834456947 254172615950275102251685421)
  ·
    refine ⟨95314730981353163344382033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254172615950275102251685421 95314730981353163344382033)
    ·
      refine ⟨71486048236014872508286525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95314730981353163344382033 71486048236014872508286525)
      ·
        refine ⟨26807268088505577190607447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71486048236014872508286525 26807268088505577190607447)
        ·
          refine ⟨40210902132758365785911171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26807268088505577190607447 40210902132758365785911171)
          ·
            refine ⟨60316353199137548678866757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40210902132758365785911171 60316353199137548678866757)
            ·
              refine ⟨11309316224838290377287517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60316353199137548678866757 11309316224838290377287517)
              ·
                refine ⟨4240993584314358891482819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11309316224838290377287517 4240993584314358891482819)
                ·
                  refine ⟨6361490376471538337224229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4240993584314358891482819 6361490376471538337224229)
                  ·
                    refine ⟨1192779445588413438229543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6361490376471538337224229 1192779445588413438229543)
                    ·
                      rfl

theorem cell23_6968789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_6968789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968789 prefixEnd_6968789 := by exact prefixLift 6968789
  have htrace : WordTrace (prefixWord ++ tailWord_6968789) baseStart_6968789 baseEnd_6968789 := by
    simpa [prefixWord, tailWord_6968789, baseEnd_6968789] using wordTrace_append hprefix tailTrace_6968789
  have hstable : (prefixWord ++ tailWord_6968789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968789).length < 2 ^ (prefixWord ++ tailWord_6968789).sum := by decide
  have hdescent : baseEnd_6968789 < baseStart_6968789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968805 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 1, 2, 6]
def baseStart_6968805 : Nat := 118140960795 + 6968805 * 2 ^ 59
def prefixEnd_6968805 : Nat := 4983230072969 + 3 ^ 40 * 6968805 * 2
def baseEnd_6968805 : Nat := 3578346552455712252088555

theorem tailTrace_6968805 : CollatzResearch.WordTrace tailWord_6968805 prefixEnd_6968805 3578346552455712252088555 := by
  unfold tailWord_6968805
  simp only [CollatzResearch.WordTrace]
  refine ⟨254173199518217136984267869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169448799678811424656178579 254173199518217136984267869)
  ·
    refine ⟨95314949819331426369100451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254173199518217136984267869 95314949819331426369100451)
    ·
      refine ⟨142972424728997139553650677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95314949819331426369100451 142972424728997139553650677)
      ·
        refine ⟨13403664818343481833154751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142972424728997139553650677 13403664818343481833154751)
        ·
          refine ⟨20105497227515222749732127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13403664818343481833154751 20105497227515222749732127)
          ·
            refine ⟨30158245841272834124598191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20105497227515222749732127 30158245841272834124598191)
            ·
              refine ⟨45237368761909251186897287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30158245841272834124598191 45237368761909251186897287)
              ·
                refine ⟨67856053142863876780345931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45237368761909251186897287 67856053142863876780345931)
                ·
                  refine ⟨101784079714295815170518897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67856053142863876780345931 101784079714295815170518897)
                  ·
                    refine ⟨76338059785721861377889173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101784079714295815170518897 76338059785721861377889173)
                    ·
                      refine ⟨3578346552455712252088555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76338059785721861377889173 3578346552455712252088555)
                      ·
                        rfl

theorem cell23_6968805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_6968805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968805 prefixEnd_6968805 := by exact prefixLift 6968805
  have htrace : WordTrace (prefixWord ++ tailWord_6968805) baseStart_6968805 baseEnd_6968805 := by
    simpa [prefixWord, tailWord_6968805, baseEnd_6968805] using wordTrace_append hprefix tailTrace_6968805
  have hstable : (prefixWord ++ tailWord_6968805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968805).length < 2 ^ (prefixWord ++ tailWord_6968805).sum := by decide
  have hdescent : baseEnd_6968805 < baseStart_6968805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968865 : List Nat := [1, 2, 3, 2, 2, 2, 1, 2, 1, 1, 6]
def baseStart_6968865 : Nat := 118140960795 + 6968865 * 2 ^ 59
def prefixEnd_6968865 : Nat := 4983230072969 + 3 ^ 40 * 6968865 * 2
def baseEnd_6968865 : Nat := 3578377361294982017338279

theorem tailTrace_6968865 : CollatzResearch.WordTrace tailWord_6968865 prefixEnd_6968865 3578377361294982017338279 := by
  unfold tailWord_6968865
  simp only [CollatzResearch.WordTrace]
  refine ⟨254175387897999767231452049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169450258598666511487634699 254175387897999767231452049)
  ·
    refine ⟨190631540923499825423589037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254175387897999767231452049 190631540923499825423589037)
    ·
      refine ⟨71486827846312434533845889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190631540923499825423589037 71486827846312434533845889)
      ·
        refine ⟨53615120884734325900384417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71486827846312434533845889 53615120884734325900384417)
        ·
          refine ⟨40211340663550744425288313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53615120884734325900384417 40211340663550744425288313)
          ·
            refine ⟨30158505497663058318966235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40211340663550744425288313 30158505497663058318966235)
            ·
              refine ⟨45237758246494587478449353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30158505497663058318966235 45237758246494587478449353)
              ·
                refine ⟨33928318684870940608837015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45237758246494587478449353 33928318684870940608837015)
                ·
                  refine ⟨50892478027306410913255523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33928318684870940608837015 50892478027306410913255523)
                  ·
                    refine ⟨76338717040959616369883285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50892478027306410913255523 76338717040959616369883285)
                    ·
                      refine ⟨3578377361294982017338279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76338717040959616369883285 3578377361294982017338279)
                      ·
                        rfl

theorem cell23_6968865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_6968865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968865 prefixEnd_6968865 := by exact prefixLift 6968865
  have htrace : WordTrace (prefixWord ++ tailWord_6968865) baseStart_6968865 baseEnd_6968865 := by
    simpa [prefixWord, tailWord_6968865, baseEnd_6968865] using wordTrace_append hprefix tailTrace_6968865
  have hstable : (prefixWord ++ tailWord_6968865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968865).length < 2 ^ (prefixWord ++ tailWord_6968865).sum := by decide
  have hdescent : baseEnd_6968865 < baseStart_6968865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968889 : List Nat := [1, 2, 1, 5, 1, 2, 3, 2, 1, 2, 3]
def baseStart_6968889 : Nat := 118140960795 + 6968889 * 2 ^ 59
def prefixEnd_6968889 : Nat := 4983230072969 + 3 ^ 40 * 6968889 * 2
def baseEnd_6968889 : Nat := 3578389684830689923438169

theorem tailTrace_6968889 : CollatzResearch.WordTrace tailWord_6968889 prefixEnd_6968889 3578389684830689923438169 := by
  unfold tailWord_6968889
  simp only [CollatzResearch.WordTrace]
  refine ⟨254176263249912819330325721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169450842166608546220217147 254176263249912819330325721)
  ·
    refine ⟨190632197437434614497744291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254176263249912819330325721 190632197437434614497744291)
    ·
      refine ⟨285948296156151921746616437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190632197437434614497744291 285948296156151921746616437)
      ·
        refine ⟨26807652764639242663745291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 285948296156151921746616437 26807652764639242663745291)
        ·
          refine ⟨40211479146958863995617937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26807652764639242663745291 40211479146958863995617937)
          ·
            refine ⟨30158609360219147996713453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40211479146958863995617937 30158609360219147996713453)
            ·
              refine ⟨11309478510082180498767545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30158609360219147996713453 11309478510082180498767545)
              ·
                refine ⟨8482108882561635374075659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11309478510082180498767545 8482108882561635374075659)
                ·
                  refine ⟨12723163323842453061113489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8482108882561635374075659 12723163323842453061113489)
                  ·
                    refine ⟨9542372492881839795835117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12723163323842453061113489 9542372492881839795835117)
                    ·
                      refine ⟨3578389684830689923438169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9542372492881839795835117 3578389684830689923438169)
                      ·
                        rfl

theorem cell23_6968889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_6968889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968889 prefixEnd_6968889 := by exact prefixLift 6968889
  have htrace : WordTrace (prefixWord ++ tailWord_6968889) baseStart_6968889 baseEnd_6968889 := by
    simpa [prefixWord, tailWord_6968889, baseEnd_6968889] using wordTrace_append hprefix tailTrace_6968889
  have hstable : (prefixWord ++ tailWord_6968889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968889).length < 2 ^ (prefixWord ++ tailWord_6968889).sum := by decide
  have hdescent : baseEnd_6968889 < baseStart_6968889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968919 : List Nat := [1, 1, 3, 2, 2, 3, 1, 4, 2, 1, 3]
def baseStart_6968919 : Nat := 118140960795 + 6968919 * 2 ^ 59
def prefixEnd_6968919 : Nat := 4983230072969 + 3 ^ 40 * 6968919 * 2
def baseEnd_6968919 : Nat := 3578405089250324806063031

theorem tailTrace_6968919 : CollatzResearch.WordTrace tailWord_6968919 prefixEnd_6968919 3578405089250324806063031 := by
  unfold tailWord_6968919
  simp only [CollatzResearch.WordTrace]
  refine ⟨254177357439804134453917811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169451571626536089635945207 254177357439804134453917811)
  ·
    refine ⟨381266036159706201680876717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254177357439804134453917811 381266036159706201680876717)
    ·
      refine ⟨142974763559889825630328769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 381266036159706201680876717 142974763559889825630328769)
      ·
        refine ⟨107231072669917369222746577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142974763559889825630328769 107231072669917369222746577)
        ·
          refine ⟨80423304502438026917059933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107231072669917369222746577 80423304502438026917059933)
          ·
            refine ⟨30158739188414260093897475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80423304502438026917059933 30158739188414260093897475)
            ·
              refine ⟨45238108782621390140846213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30158739188414260093897475 45238108782621390140846213)
              ·
                refine ⟨8482145396741510651408665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45238108782621390140846213 8482145396741510651408665)
                ·
                  refine ⟨6361609047556132988556499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8482145396741510651408665 6361609047556132988556499)
                  ·
                    refine ⟨9542413571334199482834749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6361609047556132988556499 9542413571334199482834749)
                    ·
                      refine ⟨3578405089250324806063031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9542413571334199482834749 3578405089250324806063031)
                      ·
                        rfl

theorem cell23_6968919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_6968919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968919 prefixEnd_6968919 := by exact prefixLift 6968919
  have htrace : WordTrace (prefixWord ++ tailWord_6968919) baseStart_6968919 baseEnd_6968919 := by
    simpa [prefixWord, tailWord_6968919, baseEnd_6968919] using wordTrace_append hprefix tailTrace_6968919
  have hstable : (prefixWord ++ tailWord_6968919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968919).length < 2 ^ (prefixWord ++ tailWord_6968919).sum := by decide
  have hdescent : baseEnd_6968919 < baseStart_6968919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968935 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 1, 8]
def baseStart_6968935 : Nat := 118140960795 + 6968935 * 2 ^ 59
def prefixEnd_6968935 : Nat := 4983230072969 + 3 ^ 40 * 6968935 * 2
def baseEnd_6968935 : Nat := 1192804434980265581154319

theorem tailTrace_6968935 : CollatzResearch.WordTrace tailWord_6968935 prefixEnd_6968935 1192804434980265581154319 := by
  unfold tailWord_6968935
  simp only [CollatzResearch.WordTrace]
  refine ⟨254177941007746169186500259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169451960671830779457666839 254177941007746169186500259)
  ·
    refine ⟨381266911511619253779750389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254177941007746169186500259 381266911511619253779750389)
    ·
      refine ⟨35743772954214305041851599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 381266911511619253779750389 35743772954214305041851599)
      ·
        refine ⟨53615659431321457562777399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35743772954214305041851599 53615659431321457562777399)
        ·
          refine ⟨80423489146982186344166099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53615659431321457562777399 80423489146982186344166099)
          ·
            refine ⟨120635233720473279516249149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80423489146982186344166099 120635233720473279516249149)
            ·
              refine ⟨45238212645177479818593431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120635233720473279516249149 45238212645177479818593431)
              ·
                refine ⟨67857318967766219727890147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45238212645177479818593431 67857318967766219727890147)
                ·
                  refine ⟨101785978451649329591835221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67857318967766219727890147 101785978451649329591835221)
                  ·
                    refine ⟨1192804434980265581154319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101785978451649329591835221 1192804434980265581154319)
                    ·
                      rfl

theorem cell23_6968935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_6968935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968935 prefixEnd_6968935 := by exact prefixLift 6968935
  have htrace : WordTrace (prefixWord ++ tailWord_6968935) baseStart_6968935 baseEnd_6968935 := by
    simpa [prefixWord, tailWord_6968935, baseEnd_6968935] using wordTrace_append hprefix tailTrace_6968935
  have hstable : (prefixWord ++ tailWord_6968935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968935).length < 2 ^ (prefixWord ++ tailWord_6968935).sum := by decide
  have hdescent : baseEnd_6968935 < baseStart_6968935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968936 : List Nat := [2, 1, 4, 3, 1, 1, 2, 3, 2, 1, 3]
def baseStart_6968936 : Nat := 118140960795 + 6968936 * 2 ^ 59
def prefixEnd_6968936 : Nat := 4983230072969 + 3 ^ 40 * 6968936 * 2
def baseEnd_6968936 : Nat := 3578413818421451239550453

theorem tailTrace_6968936 : CollatzResearch.WordTrace tailWord_6968936 prefixEnd_6968936 3578413818421451239550453 := by
  unfold tailWord_6968936
  simp only [CollatzResearch.WordTrace]
  refine ⟨127088988740371273178643331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169451984987161697571524441 127088988740371273178643331)
  ·
    refine ⟨190633483110556909767964997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127088988740371273178643331 190633483110556909767964997)
    ·
      refine ⟨35743778083229420581493437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190633483110556909767964997 35743778083229420581493437)
      ·
        refine ⟨13403916781211032718060039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35743778083229420581493437 13403916781211032718060039)
        ·
          refine ⟨20105875171816549077090059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13403916781211032718060039 20105875171816549077090059)
          ·
            refine ⟨30158812757724823615635089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20105875171816549077090059 30158812757724823615635089)
            ·
              refine ⟨22619109568293617711726317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30158812757724823615635089 22619109568293617711726317)
              ·
                refine ⟨8482166088110106641897369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22619109568293617711726317 8482166088110106641897369)
                ·
                  refine ⟨6361624566082579981423027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8482166088110106641897369 6361624566082579981423027)
                  ·
                    refine ⟨9542436849123869972134541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6361624566082579981423027 9542436849123869972134541)
                    ·
                      refine ⟨3578413818421451239550453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9542436849123869972134541 3578413818421451239550453)
                      ·
                        rfl

theorem cell23_6968936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_6968936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968936 prefixEnd_6968936 := by exact prefixLift 6968936
  have htrace : WordTrace (prefixWord ++ tailWord_6968936) baseStart_6968936 baseEnd_6968936 := by
    simpa [prefixWord, tailWord_6968936, baseEnd_6968936] using wordTrace_append hprefix tailTrace_6968936
  have hstable : (prefixWord ++ tailWord_6968936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968936).length < 2 ^ (prefixWord ++ tailWord_6968936).sum := by decide
  have hdescent : baseEnd_6968936 < baseStart_6968936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968945 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 4, 1, 5]
def baseStart_6968945 : Nat := 118140960795 + 6968945 * 2 ^ 59
def prefixEnd_6968945 : Nat := 4983230072969 + 3 ^ 40 * 6968945 * 2
def baseEnd_6968945 : Nat := 3578418439747341704337911

theorem tailTrace_6968945 : CollatzResearch.WordTrace tailWord_6968945 prefixEnd_6968945 3578418439747341704337911 := by
  unfold tailWord_6968945
  simp only [CollatzResearch.WordTrace]
  refine ⟨254178305737709940894364289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169452203825139960596242859 254178305737709940894364289)
  ·
    refine ⟨190633729303282455670773217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254178305737709940894364289 190633729303282455670773217)
    ·
      refine ⟨142975296977461841753079913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190633729303282455670773217 142975296977461841753079913)
      ·
        refine ⟨107231472733096381314809935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142975296977461841753079913 107231472733096381314809935)
        ·
          refine ⟨160847209099644571972214903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107231472733096381314809935 160847209099644571972214903)
          ·
            refine ⟨241270813649466857958322355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160847209099644571972214903 241270813649466857958322355)
            ·
              refine ⟨361906220474200286937483533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241270813649466857958322355 361906220474200286937483533)
              ·
                refine ⟨135714832677825107601556325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 361906220474200286937483533 135714832677825107601556325)
                ·
                  refine ⟨25446531127092207675291811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135714832677825107601556325 25446531127092207675291811)
                  ·
                    refine ⟨38169796690638311512937717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25446531127092207675291811 38169796690638311512937717)
                    ·
                      refine ⟨3578418439747341704337911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38169796690638311512937717 3578418439747341704337911)
                      ·
                        rfl

theorem cell23_6968945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_6968945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968945 prefixEnd_6968945 := by exact prefixLift 6968945
  have htrace : WordTrace (prefixWord ++ tailWord_6968945) baseStart_6968945 baseEnd_6968945 := by
    simpa [prefixWord, tailWord_6968945, baseEnd_6968945] using wordTrace_append hprefix tailTrace_6968945
  have hstable : (prefixWord ++ tailWord_6968945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968945).length < 2 ^ (prefixWord ++ tailWord_6968945).sum := by decide
  have hdescent : baseEnd_6968945 < baseStart_6968945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968955 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 4]
def baseStart_6968955 : Nat := 118140960795 + 6968955 * 2 ^ 59
def prefixEnd_6968955 : Nat := 4983230072969 + 3 ^ 40 * 6968955 * 2
def baseEnd_6968955 : Nat := 3578423574553886665212865

theorem tailTrace_6968955 : CollatzResearch.WordTrace tailWord_6968955 prefixEnd_6968955 3578423574553886665212865 := by
  unfold tailWord_6968955
  simp only [CollatzResearch.WordTrace]
  refine ⟨254178670467673712602228319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169452446978449141734818879 254178670467673712602228319)
  ·
    refine ⟨381268005701510568903342479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254178670467673712602228319 381268005701510568903342479)
    ·
      refine ⟨571902008552265853355013719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381268005701510568903342479 571902008552265853355013719)
      ·
        refine ⟨857853012828398780032520579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571902008552265853355013719 857853012828398780032520579)
        ·
          refine ⟨1286779519242598170048780869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 857853012828398780032520579 1286779519242598170048780869)
          ·
            refine ⟨241271159857987156884146413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1286779519242598170048780869 241271159857987156884146413)
            ·
              refine ⟨90476684946745183831554905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241271159857987156884146413 90476684946745183831554905)
              ·
                refine ⟨67857513710058887873666179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90476684946745183831554905 67857513710058887873666179)
                ·
                  refine ⟨101786270565088331810499269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67857513710058887873666179 101786270565088331810499269)
                  ·
                    refine ⟨19084925730954062214468613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101786270565088331810499269 19084925730954062214468613)
                    ·
                      refine ⟨3578423574553886665212865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19084925730954062214468613 3578423574553886665212865)
                      ·
                        rfl

theorem cell23_6968955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 4].length) (baseStart_6968955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968955 prefixEnd_6968955 := by exact prefixLift 6968955
  have htrace : WordTrace (prefixWord ++ tailWord_6968955) baseStart_6968955 baseEnd_6968955 := by
    simpa [prefixWord, tailWord_6968955, baseEnd_6968955] using wordTrace_append hprefix tailTrace_6968955
  have hstable : (prefixWord ++ tailWord_6968955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968955).length < 2 ^ (prefixWord ++ tailWord_6968955).sum := by decide
  have hdescent : baseEnd_6968955 < baseStart_6968955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968965 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 9]
def baseStart_6968965 : Nat := 118140960795 + 6968965 * 2 ^ 59
def prefixEnd_6968965 : Nat := 4983230072969 + 3 ^ 40 * 6968965 * 2
def baseEnd_6968965 : Nat := 397603189928936847343091

theorem tailTrace_6968965 : CollatzResearch.WordTrace tailWord_6968965 prefixEnd_6968965 397603189928936847343091 := by
  unfold tailWord_6968965
  simp only [CollatzResearch.WordTrace]
  refine ⟨254179035197637484310092349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169452690131758322873394899 254179035197637484310092349)
  ·
    refine ⟨95317138199114056616284631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254179035197637484310092349 95317138199114056616284631)
    ·
      refine ⟨142975707298671084924426947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95317138199114056616284631 142975707298671084924426947)
      ·
        refine ⟨214463560948006627386640421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142975707298671084924426947 214463560948006627386640421)
        ·
          refine ⟨40211917677751242634995079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214463560948006627386640421 40211917677751242634995079)
          ·
            refine ⟨60317876516626863952492619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40211917677751242634995079 60317876516626863952492619)
            ·
              refine ⟨90476814774940295928738929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60317876516626863952492619 90476814774940295928738929)
              ·
                refine ⟨67857611081205221946554197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90476814774940295928738929 67857611081205221946554197)
                ·
                  refine ⟨397603189928936847343091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67857611081205221946554197 397603189928936847343091)
                  ·
                    rfl

theorem cell23_6968965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 9].length) (baseStart_6968965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968965 prefixEnd_6968965 := by exact prefixLift 6968965
  have htrace : WordTrace (prefixWord ++ tailWord_6968965) baseStart_6968965 baseEnd_6968965 := by
    simpa [prefixWord, tailWord_6968965, baseEnd_6968965] using wordTrace_append hprefix tailTrace_6968965
  have hstable : (prefixWord ++ tailWord_6968965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968965).length < 2 ^ (prefixWord ++ tailWord_6968965).sum := by decide
  have hdescent : baseEnd_6968965 < baseStart_6968965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6968995 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 3, 7]
def baseStart_6968995 : Nat := 118140960795 + 6968995 * 2 ^ 59
def prefixEnd_6968995 : Nat := 4983230072969 + 3 ^ 40 * 6968995 * 2
def baseEnd_6968995 : Nat := 1192814704593355502904227

theorem tailTrace_6968995 : CollatzResearch.WordTrace tailWord_6968995 prefixEnd_6968995 1192814704593355502904227 := by
  unfold tailWord_6968995
  simp only [CollatzResearch.WordTrace]
  refine ⟨254180129387528799433684439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169453419591685866289122959 254180129387528799433684439)
  ·
    refine ⟨381270194081293199150526659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254180129387528799433684439 381270194081293199150526659)
    ·
      refine ⟨571905291121939798725789989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381270194081293199150526659 571905291121939798725789989)
      ·
        refine ⟨107232242085363712261085623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 571905291121939798725789989 107232242085363712261085623)
        ·
          refine ⟨160848363128045568391628435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107232242085363712261085623 160848363128045568391628435)
          ·
            refine ⟨241272544692068352587442653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160848363128045568391628435 241272544692068352587442653)
            ·
              refine ⟨90477204259525632220290995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241272544692068352587442653 90477204259525632220290995)
              ·
                refine ⟨135715806389288448330436493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90477204259525632220290995 135715806389288448330436493)
                ·
                  refine ⟨50893427395983168123913685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135715806389288448330436493 50893427395983168123913685)
                  ·
                    refine ⟨1192814704593355502904227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50893427395983168123913685 1192814704593355502904227)
                    ·
                      rfl

theorem cell23_6968995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 7].length) (baseStart_6968995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6968995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6968995 prefixEnd_6968995 := by exact prefixLift 6968995
  have htrace : WordTrace (prefixWord ++ tailWord_6968995) baseStart_6968995 baseEnd_6968995 := by
    simpa [prefixWord, tailWord_6968995, baseEnd_6968995] using wordTrace_append hprefix tailTrace_6968995
  have hstable : (prefixWord ++ tailWord_6968995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6968995).length < 2 ^ (prefixWord ++ tailWord_6968995).sum := by decide
  have hdescent : baseEnd_6968995 < baseStart_6968995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6968995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969106 : List Nat := [3, 2, 4, 1, 1, 1, 2, 3, 6]
def baseStart_6969106 : Nat := 118140960795 + 6969106 * 2 ^ 59
def prefixEnd_6969106 : Nat := 4983230072969 + 3 ^ 40 * 6969106 * 2
def baseEnd_6969106 : Nat := 397611234459190619380519

theorem tailTrace_6969106 : CollatzResearch.WordTrace tailWord_6969106 prefixEnd_6969106 397611234459190619380519 := by
  unfold tailWord_6969106
  simp only [CollatzResearch.WordTrace]
  refine ⟨63546044472531666347743793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169456118593417776927316781 63546044472531666347743793)
  ·
    refine ⟨47659533354398749760807845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63546044472531666347743793 47659533354398749760807845)
    ·
      refine ⟨8936162503949765580151471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47659533354398749760807845 8936162503949765580151471)
      ·
        refine ⟨13404243755924648370227207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8936162503949765580151471 13404243755924648370227207)
        ·
          refine ⟨20106365633886972555340811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13404243755924648370227207 20106365633886972555340811)
          ·
            refine ⟨30159548450830458833011217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20106365633886972555340811 30159548450830458833011217)
            ·
              refine ⟨22619661338122844124758413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30159548450830458833011217 22619661338122844124758413)
              ·
                refine ⟨8482373001796066546784405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22619661338122844124758413 8482373001796066546784405)
                ·
                  refine ⟨397611234459190619380519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8482373001796066546784405 397611234459190619380519)
                  ·
                    rfl

theorem cell23_6969106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 6].length) (baseStart_6969106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969106 prefixEnd_6969106 := by exact prefixLift 6969106
  have htrace : WordTrace (prefixWord ++ tailWord_6969106) baseStart_6969106 baseEnd_6969106 := by
    simpa [prefixWord, tailWord_6969106, baseEnd_6969106] using wordTrace_append hprefix tailTrace_6969106
  have hstable : (prefixWord ++ tailWord_6969106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969106).length < 2 ^ (prefixWord ++ tailWord_6969106).sum := by decide
  have hdescent : baseEnd_6969106 < baseStart_6969106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969116 : List Nat := [2, 2, 3, 1, 1, 2, 3, 2, 3, 1, 3]
def baseStart_6969116 : Nat := 118140960795 + 6969116 * 2 ^ 59
def prefixEnd_6969116 : Nat := 4983230072969 + 3 ^ 40 * 6969116 * 2
def baseEnd_6969116 : Nat := 3578506244939260535299625

theorem tailTrace_6969116 : CollatzResearch.WordTrace tailWord_6969116 prefixEnd_6969116 3578506244939260535299625 := by
  unfold tailWord_6969116
  simp only [CollatzResearch.WordTrace]
  refine ⟨127092271310045218549419601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169456361746726958065892801 127092271310045218549419601)
  ·
    refine ⟨95319203482533913912064701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127092271310045218549419601 95319203482533913912064701)
    ·
      refine ⟨35744701305950217717024263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95319203482533913912064701 35744701305950217717024263)
      ·
        refine ⟨53617051958925326575536395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35744701305950217717024263 53617051958925326575536395)
        ·
          refine ⟨80425577938387989863304593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53617051958925326575536395 80425577938387989863304593)
          ·
            refine ⟨60319183453790992397478445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80425577938387989863304593 60319183453790992397478445)
            ·
              refine ⟨22619693795171622149054417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60319183453790992397478445 22619693795171622149054417)
              ·
                refine ⟨16964770346378716611790813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22619693795171622149054417 16964770346378716611790813)
                ·
                  refine ⟨6361788879892018729421555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16964770346378716611790813 6361788879892018729421555)
                  ·
                    refine ⟨9542683319838028094132333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6361788879892018729421555 9542683319838028094132333)
                    ·
                      refine ⟨3578506244939260535299625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9542683319838028094132333 3578506244939260535299625)
                      ·
                        rfl

theorem cell23_6969116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_6969116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969116 prefixEnd_6969116 := by exact prefixLift 6969116
  have htrace : WordTrace (prefixWord ++ tailWord_6969116) baseStart_6969116 baseEnd_6969116 := by
    simpa [prefixWord, tailWord_6969116, baseEnd_6969116] using wordTrace_append hprefix tailTrace_6969116
  have hstable : (prefixWord ++ tailWord_6969116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969116).length < 2 ^ (prefixWord ++ tailWord_6969116).sum := by decide
  have hdescent : baseEnd_6969116 < baseStart_6969116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969119 : List Nat := [1, 1, 2, 4, 2, 1, 2, 4, 1, 5]
def baseStart_6969119 : Nat := 118140960795 + 6969119 * 2 ^ 59
def prefixEnd_6969119 : Nat := 4983230072969 + 3 ^ 40 * 6969119 * 2
def baseEnd_6969119 : Nat := 1192835928460408007854037

theorem tailTrace_6969119 : CollatzResearch.WordTrace tailWord_6969119 prefixEnd_6969119 1192835928460408007854037 := by
  unfold tailWord_6969119
  simp only [CollatzResearch.WordTrace]
  refine ⟨254184652039079568611198411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169456434692719712407465607 254184652039079568611198411)
  ·
    refine ⟨381276978058619352916797617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254184652039079568611198411 381276978058619352916797617)
    ·
      refine ⟨285957733543964514687598213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381276978058619352916797617 285957733543964514687598213)
      ·
        refine ⟨53617075039493346503924665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 285957733543964514687598213 53617075039493346503924665)
        ·
          refine ⟨40212806279620009877943499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53617075039493346503924665 40212806279620009877943499)
          ·
            refine ⟨60319209419430014816915249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40212806279620009877943499 60319209419430014816915249)
            ·
              refine ⟨45239407064572511112686437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60319209419430014816915249 45239407064572511112686437)
              ·
                refine ⟨8482388824607345833628707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45239407064572511112686437 8482388824607345833628707)
                ·
                  refine ⟨12723583236911018750443061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8482388824607345833628707 12723583236911018750443061)
                  ·
                    refine ⟨1192835928460408007854037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12723583236911018750443061 1192835928460408007854037)
                    ·
                      rfl

theorem cell23_6969119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 5].length) (baseStart_6969119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969119 prefixEnd_6969119 := by exact prefixLift 6969119
  have htrace : WordTrace (prefixWord ++ tailWord_6969119) baseStart_6969119 baseEnd_6969119 := by
    simpa [prefixWord, tailWord_6969119, baseEnd_6969119] using wordTrace_append hprefix tailTrace_6969119
  have hstable : (prefixWord ++ tailWord_6969119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969119).length < 2 ^ (prefixWord ++ tailWord_6969119).sum := by decide
  have hdescent : baseEnd_6969119 < baseStart_6969119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969150 : List Nat := [4, 2, 1, 2, 2, 1, 2, 4, 1, 1, 3]
def baseStart_6969150 : Nat := 118140960795 + 6969150 * 2 ^ 59
def prefixEnd_6969150 : Nat := 4983230072969 + 3 ^ 40 * 6969150 * 2
def baseEnd_6969150 : Nat := 3578523703281513402274469

theorem tailTrace_6969150 : CollatzResearch.WordTrace tailWord_6969150 prefixEnd_6969150 3578523703281513402274469 := by
  unfold tailWord_6969150
  simp only [CollatzResearch.WordTrace]
  refine ⟨31773222837745907613197113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169457188467978173937051269 31773222837745907613197113)
  ·
    refine ⟨23829917128309430709897835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31773222837745907613197113 23829917128309430709897835)
    ·
      refine ⟨35744875692464146064846753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23829917128309430709897835 35744875692464146064846753)
      ·
        refine ⟨26808656769348109548635065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35744875692464146064846753 26808656769348109548635065)
        ·
          refine ⟨20106492577011082161476299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26808656769348109548635065 20106492577011082161476299)
          ·
            refine ⟨30159738865516623242214449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20106492577011082161476299 30159738865516623242214449)
            ·
              refine ⟨22619804149137467431660837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30159738865516623242214449 22619804149137467431660837)
              ·
                refine ⟨4241213277963275143436407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22619804149137467431660837 4241213277963275143436407)
                ·
                  refine ⟨6361819916944912715154611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4241213277963275143436407 6361819916944912715154611)
                  ·
                    refine ⟨9542729875417369072731917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6361819916944912715154611 9542729875417369072731917)
                    ·
                      refine ⟨3578523703281513402274469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9542729875417369072731917 3578523703281513402274469)
                      ·
                        rfl

theorem cell23_6969150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_6969150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969150 prefixEnd_6969150 := by exact prefixLift 6969150
  have htrace : WordTrace (prefixWord ++ tailWord_6969150) baseStart_6969150 baseEnd_6969150 := by
    simpa [prefixWord, tailWord_6969150, baseEnd_6969150] using wordTrace_append hprefix tailTrace_6969150
  have hstable : (prefixWord ++ tailWord_6969150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969150).length < 2 ^ (prefixWord ++ tailWord_6969150).sum := by decide
  have hdescent : baseEnd_6969150 < baseStart_6969150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969152 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 4]
def baseStart_6969152 : Nat := 118140960795 + 6969152 * 2 ^ 59
def prefixEnd_6969152 : Nat := 4983230072969 + 3 ^ 40 * 6969152 * 2
def baseEnd_6969152 : Nat := 3578524730242822394449459

theorem tailTrace_6969152 : CollatzResearch.WordTrace tailWord_6969152 prefixEnd_6969152 3578524730242822394449459 := by
  unfold tailWord_6969152
  simp only [CollatzResearch.WordTrace]
  refine ⟨127092927823980007623574855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169457237098640010164766473 127092927823980007623574855)
  ·
    refine ⟨190639391735970011435362283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127092927823980007623574855 190639391735970011435362283)
    ·
      refine ⟨285959087603955017153043425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190639391735970011435362283 285959087603955017153043425)
      ·
        refine ⟨214469315702966262864782569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285959087603955017153043425 214469315702966262864782569)
        ·
          refine ⟨160851986777224697148586927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214469315702966262864782569 160851986777224697148586927)
          ·
            refine ⟨241277980165837045722880391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160851986777224697148586927 241277980165837045722880391)
            ·
              refine ⟨361916970248755568584320587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241277980165837045722880391 361916970248755568584320587)
              ·
                refine ⟨542875455373133352876480881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361916970248755568584320587 542875455373133352876480881)
                ·
                  refine ⟨407156591529850014657360661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 542875455373133352876480881 407156591529850014657360661)
                  ·
                    refine ⟨19085465227961719437063781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 407156591529850014657360661 19085465227961719437063781)
                    ·
                      refine ⟨3578524730242822394449459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19085465227961719437063781 3578524730242822394449459)
                      ·
                        rfl

theorem cell23_6969152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_6969152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969152 prefixEnd_6969152 := by exact prefixLift 6969152
  have htrace : WordTrace (prefixWord ++ tailWord_6969152) baseStart_6969152 baseEnd_6969152 := by
    simpa [prefixWord, tailWord_6969152, baseEnd_6969152] using wordTrace_append hprefix tailTrace_6969152
  have hstable : (prefixWord ++ tailWord_6969152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969152).length < 2 ^ (prefixWord ++ tailWord_6969152).sum := by decide
  have hdescent : baseEnd_6969152 < baseStart_6969152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969159 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 5, 2, 3]
def baseStart_6969159 : Nat := 118140960795 + 6969159 * 2 ^ 59
def prefixEnd_6969159 : Nat := 4983230072969 + 3 ^ 40 * 6969159 * 2
def baseEnd_6969159 : Nat := 3578528324607403867061927

theorem tailTrace_6969159 : CollatzResearch.WordTrace tailWord_6969159 prefixEnd_6969159 3578528324607403867061927 := by
  unfold tailWord_6969159
  simp only [CollatzResearch.WordTrace]
  refine ⟨254186110958934655442654531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169457407305956436961769687 254186110958934655442654531)
  ·
    refine ⟨381279166438401983163981797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254186110958934655442654531 381279166438401983163981797)
    ·
      refine ⟨71489843707200371843246587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 381279166438401983163981797 71489843707200371843246587)
      ·
        refine ⟨107234765560800557764869881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71489843707200371843246587 107234765560800557764869881)
        ·
          refine ⟨80426074170600418323652411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107234765560800557764869881 80426074170600418323652411)
          ·
            refine ⟨120639111255900627485478617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80426074170600418323652411 120639111255900627485478617)
            ·
              refine ⟨90479333441925470614108963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120639111255900627485478617 90479333441925470614108963)
              ·
                refine ⟨135719000162888205921163445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90479333441925470614108963 135719000162888205921163445)
                ·
                  refine ⟨12723656265270769305109073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135719000162888205921163445 12723656265270769305109073)
                  ·
                    refine ⟨9542742198953076978831805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12723656265270769305109073 9542742198953076978831805)
                    ·
                      refine ⟨3578528324607403867061927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9542742198953076978831805 3578528324607403867061927)
                      ·
                        rfl

theorem cell23_6969159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_6969159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969159 prefixEnd_6969159 := by exact prefixLift 6969159
  have htrace : WordTrace (prefixWord ++ tailWord_6969159) baseStart_6969159 baseEnd_6969159 := by
    simpa [prefixWord, tailWord_6969159, baseEnd_6969159] using wordTrace_append hprefix tailTrace_6969159
  have hstable : (prefixWord ++ tailWord_6969159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969159).length < 2 ^ (prefixWord ++ tailWord_6969159).sum := by decide
  have hdescent : baseEnd_6969159 < baseStart_6969159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969162 : List Nat := [3, 1, 2, 1, 1, 1, 4, 10]
def baseStart_6969162 : Nat := 118140960795 + 6969162 * 2 ^ 59
def prefixEnd_6969162 : Nat := 4983230072969 + 3 ^ 40 * 6969162 * 2
def baseEnd_6969162 : Nat := 132538143149976568715719

theorem tailTrace_6969162 : CollatzResearch.WordTrace tailWord_6969162 prefixEnd_6969162 132538143149976568715719 := by
  unfold tailWord_6969162
  simp only [CollatzResearch.WordTrace]
  refine ⟨63546555094480946738753435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169457480251949191303342493 63546555094480946738753435)
  ·
    refine ⟨95319832641721420108130153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63546555094480946738753435 95319832641721420108130153)
    ·
      refine ⟨71489874481291065081097615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95319832641721420108130153 71489874481291065081097615)
      ·
        refine ⟨107234811721936597621646423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71489874481291065081097615 107234811721936597621646423)
        ·
          refine ⟨160852217582904896432469635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107234811721936597621646423 160852217582904896432469635)
          ·
            refine ⟨241278326374357344648704453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160852217582904896432469635 241278326374357344648704453)
            ·
              refine ⟨45239686195192002121632085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 241278326374357344648704453 45239686195192002121632085)
              ·
                refine ⟨132538143149976568715719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 45239686195192002121632085 132538143149976568715719)
                ·
                  rfl

theorem cell23_6969162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 10].length) (baseStart_6969162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969162 prefixEnd_6969162 := by exact prefixLift 6969162
  have htrace : WordTrace (prefixWord ++ tailWord_6969162) baseStart_6969162 baseEnd_6969162 := by
    simpa [prefixWord, tailWord_6969162, baseEnd_6969162] using wordTrace_append hprefix tailTrace_6969162
  have hstable : (prefixWord ++ tailWord_6969162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969162).length < 2 ^ (prefixWord ++ tailWord_6969162).sum := by decide
  have hdescent : baseEnd_6969162 < baseStart_6969162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969169 : List Nat := [1, 2, 2, 1, 5, 2, 1, 1, 1, 1, 6]
def baseStart_6969169 : Nat := 118140960795 + 6969169 * 2 ^ 59
def prefixEnd_6969169 : Nat := 4983230072969 + 3 ^ 40 * 6969169 * 2
def baseEnd_6969169 : Nat := 3578533459413948827936881

theorem tailTrace_6969169 : CollatzResearch.WordTrace tailWord_6969169 prefixEnd_6969169 3578533459413948827936881 := by
  unfold tailWord_6969169
  simp only [CollatzResearch.WordTrace]
  refine ⟨254186475688898427150518561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169457650459265618100345707 254186475688898427150518561)
  ·
    refine ⟨190639856766673820362888921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254186475688898427150518561 190639856766673820362888921)
    ·
      refine ⟨142979892575005365272166691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190639856766673820362888921 142979892575005365272166691)
      ·
        refine ⟨214469838862508047908250037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142979892575005365272166691 214469838862508047908250037)
        ·
          refine ⟨20106547393360129491398441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 214469838862508047908250037 20106547393360129491398441)
          ·
            refine ⟨15079910545020097118548831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20106547393360129491398441 15079910545020097118548831)
            ·
              refine ⟨22619865817530145677823247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15079910545020097118548831 22619865817530145677823247)
              ·
                refine ⟨33929798726295218516734871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22619865817530145677823247 33929798726295218516734871)
                ·
                  refine ⟨50894698089442827775102307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33929798726295218516734871 50894698089442827775102307)
                  ·
                    refine ⟨76342047134164241662653461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50894698089442827775102307 76342047134164241662653461)
                    ·
                      refine ⟨3578533459413948827936881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76342047134164241662653461 3578533459413948827936881)
                      ·
                        rfl

theorem cell23_6969169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_6969169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969169 prefixEnd_6969169 := by exact prefixLift 6969169
  have htrace : WordTrace (prefixWord ++ tailWord_6969169) baseStart_6969169 baseEnd_6969169 := by
    simpa [prefixWord, tailWord_6969169, baseEnd_6969169] using wordTrace_append hprefix tailTrace_6969169
  have hstable : (prefixWord ++ tailWord_6969169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969169).length < 2 ^ (prefixWord ++ tailWord_6969169).sum := by decide
  have hdescent : baseEnd_6969169 < baseStart_6969169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969173 : List Nat := [1, 3, 2, 2, 2, 2, 2, 2, 3, 2, 2]
def baseStart_6969173 : Nat := 118140960795 + 6969173 * 2 ^ 59
def prefixEnd_6969173 : Nat := 4983230072969 + 3 ^ 40 * 6969173 * 2
def baseEnd_6969173 : Nat := 3578535513336566812286863

theorem tailTrace_6969173 : CollatzResearch.WordTrace tailWord_6969173 prefixEnd_6969173 3578535513336566812286863 := by
  unfold tailWord_6969173
  simp only [CollatzResearch.WordTrace]
  refine ⟨254186621580883935833664173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169457747720589290555776115 254186621580883935833664173)
  ·
    refine ⟨95319983092831475937624065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254186621580883935833664173 95319983092831475937624065)
    ·
      refine ⟨71489987319623606953218049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95319983092831475937624065 71489987319623606953218049)
      ·
        refine ⟨53617490489717705214913537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71489987319623606953218049 53617490489717705214913537)
        ·
          refine ⟨40213117867288278911185153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53617490489717705214913537 40213117867288278911185153)
          ·
            refine ⟨30159838400466209183388865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40213117867288278911185153 30159838400466209183388865)
            ·
              refine ⟨22619878800349656887541649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30159838400466209183388865 22619878800349656887541649)
              ·
                refine ⟨16964909100262242665656237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22619878800349656887541649 16964909100262242665656237)
                ·
                  refine ⟨6361840912598340999621089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16964909100262242665656237 6361840912598340999621089)
                  ·
                    refine ⟨4771380684448755749715817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6361840912598340999621089 4771380684448755749715817)
                    ·
                      refine ⟨3578535513336566812286863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4771380684448755749715817 3578535513336566812286863)
                      ·
                        rfl

theorem cell23_6969173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_6969173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969173 prefixEnd_6969173 := by exact prefixLift 6969173
  have htrace : WordTrace (prefixWord ++ tailWord_6969173) baseStart_6969173 baseEnd_6969173 := by
    simpa [prefixWord, tailWord_6969173, baseEnd_6969173] using wordTrace_append hprefix tailTrace_6969173
  have hstable : (prefixWord ++ tailWord_6969173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969173).length < 2 ^ (prefixWord ++ tailWord_6969173).sum := by decide
  have hdescent : baseEnd_6969173 < baseStart_6969173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969189 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 3, 3, 3]
def baseStart_6969189 : Nat := 118140960795 + 6969189 * 2 ^ 59
def prefixEnd_6969189 : Nat := 4983230072969 + 3 ^ 40 * 6969189 * 2
def baseEnd_6969189 : Nat := 3578543729027038749686789

theorem tailTrace_6969189 : CollatzResearch.WordTrace tailWord_6969189 prefixEnd_6969189 3578543729027038749686789 := by
  unfold tailWord_6969189
  simp only [CollatzResearch.WordTrace]
  refine ⟨254187205148825970566246621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169458136765883980377497747 254187205148825970566246621)
  ·
    refine ⟨95320201930809738962342483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254187205148825970566246621 95320201930809738962342483)
    ·
      refine ⟨142980302896214608443513725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95320201930809738962342483 142980302896214608443513725)
      ·
        refine ⟨53617613586080478166317647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142980302896214608443513725 53617613586080478166317647)
        ·
          refine ⟨80426420379120717249476471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53617613586080478166317647 80426420379120717249476471)
          ·
            refine ⟨120639630568681075874214707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80426420379120717249476471 120639630568681075874214707)
            ·
              refine ⟨180959445853021613811322061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120639630568681075874214707 180959445853021613811322061)
              ·
                refine ⟨67859792194883105179245773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180959445853021613811322061 67859792194883105179245773)
                ·
                  refine ⟨25447422073081164442217165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67859792194883105179245773 25447422073081164442217165)
                  ·
                    refine ⟨9542783277405436665831437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25447422073081164442217165 9542783277405436665831437)
                    ·
                      refine ⟨3578543729027038749686789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9542783277405436665831437 3578543729027038749686789)
                      ·
                        rfl

theorem cell23_6969189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_6969189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969189 prefixEnd_6969189 := by exact prefixLift 6969189
  have htrace : WordTrace (prefixWord ++ tailWord_6969189) baseStart_6969189 baseEnd_6969189 := by
    simpa [prefixWord, tailWord_6969189, baseEnd_6969189] using wordTrace_append hprefix tailTrace_6969189
  have hstable : (prefixWord ++ tailWord_6969189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969189).length < 2 ^ (prefixWord ++ tailWord_6969189).sum := by decide
  have hdescent : baseEnd_6969189 < baseStart_6969189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969216 : List Nat := [2, 1, 1, 2, 1, 2, 4, 2, 3, 3, 2]
def baseStart_6969216 : Nat := 118140960795 + 6969216 * 2 ^ 59
def prefixEnd_6969216 : Nat := 4983230072969 + 3 ^ 40 * 6969216 * 2
def baseEnd_6969216 : Nat := 3578557593004710144049165

theorem tailTrace_6969216 : CollatzResearch.WordTrace tailWord_6969216 prefixEnd_6969216 3578557593004710144049165 := by
  unfold tailWord_6969216
  simp only [CollatzResearch.WordTrace]
  refine ⟨127094094959864077088739751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169458793279818769451653001 127094094959864077088739751)
  ·
    refine ⟨190641142439796115633109627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127094094959864077088739751 190641142439796115633109627)
    ·
      refine ⟨285961713659694173449664441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190641142439796115633109627 285961713659694173449664441)
      ·
        refine ⟨214471285244770630087248331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285961713659694173449664441 214471285244770630087248331)
        ·
          refine ⟨321706927867155945130872497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214471285244770630087248331 321706927867155945130872497)
          ·
            refine ⟨241280195900366958848154373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321706927867155945130872497 241280195900366958848154373)
            ·
              refine ⟨45240036731318804784028945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 241280195900366958848154373 45240036731318804784028945)
              ·
                refine ⟨33930027548489103588021709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45240036731318804784028945 33930027548489103588021709)
                ·
                  refine ⟨12723760330683413845508141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33930027548489103588021709 12723760330683413845508141)
                  ·
                    refine ⟨4771410124006280192065553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12723760330683413845508141 4771410124006280192065553)
                    ·
                      refine ⟨3578557593004710144049165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4771410124006280192065553 3578557593004710144049165)
                      ·
                        rfl

theorem cell23_6969216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 3, 3, 2].length) (baseStart_6969216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969216 prefixEnd_6969216 := by exact prefixLift 6969216
  have htrace : WordTrace (prefixWord ++ tailWord_6969216) baseStart_6969216 baseEnd_6969216 := by
    simpa [prefixWord, tailWord_6969216, baseEnd_6969216] using wordTrace_append hprefix tailTrace_6969216
  have hstable : (prefixWord ++ tailWord_6969216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969216).length < 2 ^ (prefixWord ++ tailWord_6969216).sum := by decide
  have hdescent : baseEnd_6969216 < baseStart_6969216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969217 : List Nat := [1, 2, 4, 4, 1, 2, 2, 1, 2, 4]
def baseStart_6969217 : Nat := 118140960795 + 6969217 * 2 ^ 59
def prefixEnd_6969217 : Nat := 4983230072969 + 3 ^ 40 * 6969217 * 2
def baseEnd_6969217 : Nat := 1192852702161788213378887

theorem tailTrace_6969217 : CollatzResearch.WordTrace tailWord_6969217 prefixEnd_6969217 1192852702161788213378887 := by
  unfold tailWord_6969217
  simp only [CollatzResearch.WordTrace]
  refine ⟨254188226392724531348265905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169458817595149687565510603 254188226392724531348265905)
  ·
    refine ⟨190641169794543398511199429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254188226392724531348265905 190641169794543398511199429)
    ·
      refine ⟨35745219336476887220849893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190641169794543398511199429 35745219336476887220849893)
      ·
        refine ⟨6702228625589416353909355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35745219336476887220849893 6702228625589416353909355)
        ·
          refine ⟨10053342938384124530864033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6702228625589416353909355 10053342938384124530864033)
          ·
            refine ⟨7540007203788093398148025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10053342938384124530864033 7540007203788093398148025)
            ·
              refine ⟨5655005402841070048611019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7540007203788093398148025 5655005402841070048611019)
              ·
                refine ⟨8482508104261605072916529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5655005402841070048611019 8482508104261605072916529)
                ·
                  refine ⟨6361881078196203804687397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8482508104261605072916529 6361881078196203804687397)
                  ·
                    refine ⟨1192852702161788213378887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6361881078196203804687397 1192852702161788213378887)
                    ·
                      rfl

theorem cell23_6969217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_6969217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969217 prefixEnd_6969217 := by exact prefixLift 6969217
  have htrace : WordTrace (prefixWord ++ tailWord_6969217) baseStart_6969217 baseEnd_6969217 := by
    simpa [prefixWord, tailWord_6969217, baseEnd_6969217] using wordTrace_append hprefix tailTrace_6969217
  have hstable : (prefixWord ++ tailWord_6969217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969217).length < 2 ^ (prefixWord ++ tailWord_6969217).sum := by decide
  have hdescent : baseEnd_6969217 < baseStart_6969217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969233 : List Nat := [1, 2, 2, 1, 1, 1, 7, 2, 1, 3, 2]
def baseStart_6969233 : Nat := 118140960795 + 6969233 * 2 ^ 59
def prefixEnd_6969233 : Nat := 4983230072969 + 3 ^ 40 * 6969233 * 2
def baseEnd_6969233 : Nat := 3578566322175836577536587

theorem tailTrace_6969233 : CollatzResearch.WordTrace tailWord_6969233 prefixEnd_6969233 3578566322175836577536587 := by
  unfold tailWord_6969233
  simp only [CollatzResearch.WordTrace]
  refine ⟨254188809960666566080848353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169459206640444377387232235 254188809960666566080848353)
  ·
    refine ⟨190641607470499924560636265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254188809960666566080848353 190641607470499924560636265)
    ·
      refine ⟨142981205602874943420477199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190641607470499924560636265 142981205602874943420477199)
      ·
        refine ⟨214471808404312415130715799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142981205602874943420477199 214471808404312415130715799)
        ·
          refine ⟨321707712606468622696073699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214471808404312415130715799 321707712606468622696073699)
          ·
            refine ⟨482561568909702934044110549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321707712606468622696073699 482561568909702934044110549)
            ·
              refine ⟨11310036771321162516658841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 482561568909702934044110549 11310036771321162516658841)
              ·
                refine ⟨8482527578490871887494131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11310036771321162516658841 8482527578490871887494131)
                ·
                  refine ⟨12723791367736307831241197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8482527578490871887494131 12723791367736307831241197)
                  ·
                    refine ⟨4771421762901115436715449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12723791367736307831241197 4771421762901115436715449)
                    ·
                      refine ⟨3578566322175836577536587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4771421762901115436715449 3578566322175836577536587)
                      ·
                        rfl

theorem cell23_6969233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 3, 2].length) (baseStart_6969233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969233 prefixEnd_6969233 := by exact prefixLift 6969233
  have htrace : WordTrace (prefixWord ++ tailWord_6969233) baseStart_6969233 baseEnd_6969233 := by
    simpa [prefixWord, tailWord_6969233, baseEnd_6969233] using wordTrace_append hprefix tailTrace_6969233
  have hstable : (prefixWord ++ tailWord_6969233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969233).length < 2 ^ (prefixWord ++ tailWord_6969233).sum := by decide
  have hdescent : baseEnd_6969233 < baseStart_6969233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969356 : List Nat := [2, 2, 1, 2, 3, 1, 1, 3, 1, 4, 3]
def baseStart_6969356 : Nat := 118140960795 + 6969356 * 2 ^ 59
def prefixEnd_6969356 : Nat := 4983230072969 + 3 ^ 40 * 6969356 * 2
def baseEnd_6969356 : Nat := 3578629480296339596298521

theorem tailTrace_6969356 : CollatzResearch.WordTrace tailWord_6969356 prefixEnd_6969356 3578629480296339596298521 := by
  unfold tailWord_6969356
  simp only [CollatzResearch.WordTrace]
  refine ⟨127096648069610479043787961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169462197426147305391717281 127096648069610479043787961)
  ·
    refine ⟨95322486052207859282840971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127096648069610479043787961 95322486052207859282840971)
    ·
      refine ⟨142983729078311788924261457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95322486052207859282840971 142983729078311788924261457)
      ·
        refine ⟨107237796808733841693196093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142983729078311788924261457 107237796808733841693196093)
        ·
          refine ⟨40214173803275190634948535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107237796808733841693196093 40214173803275190634948535)
          ·
            refine ⟨60321260704912785952422803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40214173803275190634948535 60321260704912785952422803)
            ·
              refine ⟨90481891057369178928634205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60321260704912785952422803 90481891057369178928634205)
              ·
                refine ⟨33930709146513442098237827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90481891057369178928634205 33930709146513442098237827)
                ·
                  refine ⟨50896063719770163147356741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33930709146513442098237827 50896063719770163147356741)
                  ·
                    refine ⟨9543011947456905590129389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50896063719770163147356741 9543011947456905590129389)
                    ·
                      refine ⟨3578629480296339596298521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9543011947456905590129389 3578629480296339596298521)
                      ·
                        rfl

theorem cell23_6969356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_6969356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969356 prefixEnd_6969356 := by exact prefixLift 6969356
  have htrace : WordTrace (prefixWord ++ tailWord_6969356) baseStart_6969356 baseEnd_6969356 := by
    simpa [prefixWord, tailWord_6969356, baseEnd_6969356] using wordTrace_append hprefix tailTrace_6969356
  have hstable : (prefixWord ++ tailWord_6969356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969356).length < 2 ^ (prefixWord ++ tailWord_6969356).sum := by decide
  have hdescent : baseEnd_6969356 < baseStart_6969356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969373 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 4, 2, 3]
def baseStart_6969373 : Nat := 118140960795 + 6969373 * 2 ^ 59
def prefixEnd_6969373 : Nat := 4983230072969 + 3 ^ 40 * 6969373 * 2
def baseEnd_6969373 : Nat := 3578638209467466029785943

theorem tailTrace_6969373 : CollatzResearch.WordTrace tailWord_6969373 prefixEnd_6969373 3578638209467466029785943 := by
  unfold tailWord_6969373
  simp only [CollatzResearch.WordTrace]
  refine ⟨254193916180159369990944773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169462610786772913327296515 254193916180159369990944773)
  ·
    refine ⟨47661359283779881873302145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254193916180159369990944773 47661359283779881873302145)
    ·
      refine ⟨35746019462834911404976609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47661359283779881873302145 35746019462834911404976609)
      ·
        refine ⟨26809514597126183553732457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35746019462834911404976609 26809514597126183553732457)
        ·
          refine ⟨20107135947844637665299343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26809514597126183553732457 20107135947844637665299343)
          ·
            refine ⟨30160703921766956497949015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20107135947844637665299343 30160703921766956497949015)
            ·
              refine ⟨45241055882650434746923523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30160703921766956497949015 45241055882650434746923523)
              ·
                refine ⟨67861583823975652120385285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45241055882650434746923523 67861583823975652120385285)
                ·
                  refine ⟨12724046966995434772572241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67861583823975652120385285 12724046966995434772572241)
                  ·
                    refine ⟨9543035225246576079429181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12724046966995434772572241 9543035225246576079429181)
                    ·
                      refine ⟨3578638209467466029785943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9543035225246576079429181 3578638209467466029785943)
                      ·
                        rfl

theorem cell23_6969373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_6969373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969373 prefixEnd_6969373 := by exact prefixLift 6969373
  have htrace : WordTrace (prefixWord ++ tailWord_6969373) baseStart_6969373 baseEnd_6969373 := by
    simpa [prefixWord, tailWord_6969373, baseEnd_6969373] using wordTrace_append hprefix tailTrace_6969373
  have hstable : (prefixWord ++ tailWord_6969373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969373).length < 2 ^ (prefixWord ++ tailWord_6969373).sum := by decide
  have hdescent : baseEnd_6969373 < baseStart_6969373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969393 : List Nat := [1, 2, 2, 3, 1, 3, 4, 1, 6]
def baseStart_6969393 : Nat := 118140960795 + 6969393 * 2 ^ 59
def prefixEnd_6969393 : Nat := 4983230072969 + 3 ^ 40 * 6969393 * 2
def baseEnd_6969393 : Nat := 397627608786728439059539

theorem tailTrace_6969393 : CollatzResearch.WordTrace tailWord_6969393 prefixEnd_6969393 397627608786728439059539 := by
  unfold tailWord_6969393
  simp only [CollatzResearch.WordTrace]
  refine ⟨254194645640086913406672833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169463097093391275604448555 254194645640086913406672833)
  ·
    refine ⟨190645984230065185055004625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254194645640086913406672833 190645984230065185055004625)
    ·
      refine ⟨142984488172548888791253469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190645984230065185055004625 142984488172548888791253469)
      ·
        refine ⟨53619183064705833296720051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142984488172548888791253469 53619183064705833296720051)
        ·
          refine ⟨80428774597058749945080077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53619183064705833296720051 80428774597058749945080077)
          ·
            refine ⟨30160790473897031229405029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80428774597058749945080077 30160790473897031229405029)
            ·
              refine ⟨5655148213855693355513443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30160790473897031229405029 5655148213855693355513443)
              ·
                refine ⟨8482722320783540033270165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5655148213855693355513443 8482722320783540033270165)
                ·
                  refine ⟨397627608786728439059539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8482722320783540033270165 397627608786728439059539)
                  ·
                    rfl

theorem cell23_6969393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 6].length) (baseStart_6969393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969393 prefixEnd_6969393 := by exact prefixLift 6969393
  have htrace : WordTrace (prefixWord ++ tailWord_6969393) baseStart_6969393 baseEnd_6969393 := by
    simpa [prefixWord, tailWord_6969393, baseEnd_6969393] using wordTrace_append hprefix tailTrace_6969393
  have hstable : (prefixWord ++ tailWord_6969393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969393).length < 2 ^ (prefixWord ++ tailWord_6969393).sum := by decide
  have hdescent : baseEnd_6969393 < baseStart_6969393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969453 : List Nat := [1, 5, 1, 1, 2, 1, 4, 1, 1, 6]
def baseStart_6969453 : Nat := 118140960795 + 6969453 * 2 ^ 59
def prefixEnd_6969453 : Nat := 4983230072969 + 3 ^ 40 * 6969453 * 2
def baseEnd_6969453 : Nat := 1192893095973275238928525

theorem tailTrace_6969453 : CollatzResearch.WordTrace tailWord_6969453 prefixEnd_6969453 1192893095973275238928525 := by
  unfold tailWord_6969453
  simp only [CollatzResearch.WordTrace]
  refine ⟨254196834019869543653857013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169464556013246362435904675 254196834019869543653857013)
  ·
    refine ⟨23830953189362769717549095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 254196834019869543653857013 23830953189362769717549095)
    ·
      refine ⟨35746429784044154576323643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23830953189362769717549095 35746429784044154576323643)
      ·
        refine ⟨53619644676066231864485465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35746429784044154576323643 53619644676066231864485465)
        ·
          refine ⟨40214733507049673898364099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53619644676066231864485465 40214733507049673898364099)
          ·
            refine ⟨60322100260574510847546149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40214733507049673898364099 60322100260574510847546149)
            ·
              refine ⟨11310393798857720783914903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60322100260574510847546149 11310393798857720783914903)
              ·
                refine ⟨16965590698286581175872355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11310393798857720783914903 16965590698286581175872355)
                ·
                  refine ⟨25448386047429871763808533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16965590698286581175872355 25448386047429871763808533)
                  ·
                    refine ⟨1192893095973275238928525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25448386047429871763808533 1192893095973275238928525)
                    ·
                      rfl

theorem cell23_6969453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_6969453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969453 prefixEnd_6969453 := by exact prefixLift 6969453
  have htrace : WordTrace (prefixWord ++ tailWord_6969453) baseStart_6969453 baseEnd_6969453 := by
    simpa [prefixWord, tailWord_6969453, baseEnd_6969453] using wordTrace_append hprefix tailTrace_6969453
  have hstable : (prefixWord ++ tailWord_6969453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969453).length < 2 ^ (prefixWord ++ tailWord_6969453).sum := by decide
  have hdescent : baseEnd_6969453 < baseStart_6969453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969463 : List Nat := [1, 1, 3, 1, 1, 5, 2, 1, 3, 2, 3]
def baseStart_6969463 : Nat := 118140960795 + 6969463 * 2 ^ 59
def prefixEnd_6969463 : Nat := 4983230072969 + 3 ^ 40 * 6969463 * 2
def baseEnd_6969463 : Nat := 3578684422726370677660529

theorem tailTrace_6969463 : CollatzResearch.WordTrace tailWord_6969463 prefixEnd_6969463 3578684422726370677660529 := by
  unfold tailWord_6969463
  simp only [CollatzResearch.WordTrace]
  refine ⟨254197198749833315361721043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169464799166555543574480695 254197198749833315361721043)
  ·
    refine ⟨381295798124749973042581565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254197198749833315361721043 381295798124749973042581565)
    ·
      refine ⟨142985924296781239890968087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 381295798124749973042581565 142985924296781239890968087)
      ·
        refine ⟨214478886445171859836452131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142985924296781239890968087 214478886445171859836452131)
        ·
          refine ⟨321718329667757789754678197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214478886445171859836452131 321718329667757789754678197)
          ·
            refine ⟨30161093406352292789501081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 321718329667757789754678197 30161093406352292789501081)
            ·
              refine ⟨22620820054764219592125811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30161093406352292789501081 22620820054764219592125811)
              ·
                refine ⟨33931230082146329388188717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22620820054764219592125811 33931230082146329388188717)
                ·
                  refine ⟨12724211280804873520570769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33931230082146329388188717 12724211280804873520570769)
                  ·
                    refine ⟨9543158460603655140428077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12724211280804873520570769 9543158460603655140428077)
                    ·
                      refine ⟨3578684422726370677660529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9543158460603655140428077 3578684422726370677660529)
                      ·
                        rfl

theorem cell23_6969463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 2, 3].length) (baseStart_6969463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969463 prefixEnd_6969463 := by exact prefixLift 6969463
  have htrace : WordTrace (prefixWord ++ tailWord_6969463) baseStart_6969463 baseEnd_6969463 := by
    simpa [prefixWord, tailWord_6969463, baseEnd_6969463] using wordTrace_append hprefix tailTrace_6969463
  have hstable : (prefixWord ++ tailWord_6969463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969463).length < 2 ^ (prefixWord ++ tailWord_6969463).sum := by decide
  have hdescent : baseEnd_6969463 < baseStart_6969463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969477 : List Nat := [1, 3, 1, 1, 5, 3, 2, 1, 1, 1, 4]
def baseStart_6969477 : Nat := 118140960795 + 6969477 * 2 ^ 59
def prefixEnd_6969477 : Nat := 4983230072969 + 3 ^ 40 * 6969477 * 2
def baseEnd_6969477 : Nat := 3578691611455533622885465

theorem tailTrace_6969477 : CollatzResearch.WordTrace tailWord_6969477 prefixEnd_6969477 3578691611455533622885465 := by
  unfold tailWord_6969477
  simp only [CollatzResearch.WordTrace]
  refine ⟨254197709371782595752730685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169465139581188397168487123 254197709371782595752730685)
  ·
    refine ⟨95324141014418473407274007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254197709371782595752730685 95324141014418473407274007)
    ·
      refine ⟨142986211521627710110911011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95324141014418473407274007 142986211521627710110911011)
      ·
        refine ⟨214479317282441565166366517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142986211521627710110911011 214479317282441565166366517)
        ·
          refine ⟨20107435995228896734346861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 214479317282441565166366517 20107435995228896734346861)
          ·
            refine ⟨7540288498210836275380073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20107435995228896734346861 7540288498210836275380073)
            ·
              refine ⟨5655216373658127206535055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7540288498210836275380073 5655216373658127206535055)
              ·
                refine ⟨8482824560487190809802583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5655216373658127206535055 8482824560487190809802583)
                ·
                  refine ⟨12724236840730786214703875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8482824560487190809802583 12724236840730786214703875)
                  ·
                    refine ⟨19086355261096179322055813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12724236840730786214703875 19086355261096179322055813)
                    ·
                      refine ⟨3578691611455533622885465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19086355261096179322055813 3578691611455533622885465)
                      ·
                        rfl

theorem cell23_6969477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 1, 1, 4].length) (baseStart_6969477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969477 prefixEnd_6969477 := by exact prefixLift 6969477
  have htrace : WordTrace (prefixWord ++ tailWord_6969477) baseStart_6969477 baseEnd_6969477 := by
    simpa [prefixWord, tailWord_6969477, baseEnd_6969477] using wordTrace_append hprefix tailTrace_6969477
  have hstable : (prefixWord ++ tailWord_6969477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969477).length < 2 ^ (prefixWord ++ tailWord_6969477).sum := by decide
  have hdescent : baseEnd_6969477 < baseStart_6969477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969514 : List Nat := [3, 1, 5, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_6969514 : Nat := 118140960795 + 6969514 * 2 ^ 59
def prefixEnd_6969514 : Nat := 4983230072969 + 3 ^ 40 * 6969514 * 2
def baseEnd_6969514 : Nat := 3578710610239749978122795

theorem tailTrace_6969514 : CollatzResearch.WordTrace tailWord_6969514 prefixEnd_6969514 3578710610239749978122795 := by
  unfold tailWord_6969514
  simp only [CollatzResearch.WordTrace]
  refine ⟨63549764718162137767956899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169466039248432367381218397 63549764718162137767956899)
  ·
    refine ⟨95324647077243206651935349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63549764718162137767956899 95324647077243206651935349)
    ·
      refine ⟨8936685663491550623618939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95324647077243206651935349 8936685663491550623618939)
      ·
        refine ⟨13405028495237325935428409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8936685663491550623618939 13405028495237325935428409)
        ·
          refine ⟨10053771371427994451571307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13405028495237325935428409 10053771371427994451571307)
          ·
            refine ⟨15080657057141991677356961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10053771371427994451571307 15080657057141991677356961)
            ·
              refine ⟨11310492792856493758017721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15080657057141991677356961 11310492792856493758017721)
              ·
                refine ⟨8482869594642370318513291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11310492792856493758017721 8482869594642370318513291)
                ·
                  refine ⟨12724304391963555477769937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8482869594642370318513291 12724304391963555477769937)
                  ·
                    refine ⟨9543228293972666608327453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12724304391963555477769937 9543228293972666608327453)
                    ·
                      refine ⟨3578710610239749978122795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9543228293972666608327453 3578710610239749978122795)
                      ·
                        rfl

theorem cell23_6969514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_6969514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969514 prefixEnd_6969514 := by exact prefixLift 6969514
  have htrace : WordTrace (prefixWord ++ tailWord_6969514) baseStart_6969514 baseEnd_6969514 := by
    simpa [prefixWord, tailWord_6969514, baseEnd_6969514] using wordTrace_append hprefix tailTrace_6969514
  have hstable : (prefixWord ++ tailWord_6969514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969514).length < 2 ^ (prefixWord ++ tailWord_6969514).sum := by decide
  have hdescent : baseEnd_6969514 < baseStart_6969514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969516 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 4]
def baseStart_6969516 : Nat := 118140960795 + 6969516 * 2 ^ 59
def prefixEnd_6969516 : Nat := 4983230072969 + 3 ^ 40 * 6969516 * 2
def baseEnd_6969516 : Nat := 3578711637201058970297785

theorem tailTrace_6969516 : CollatzResearch.WordTrace tailWord_6969516 prefixEnd_6969516 3578711637201058970297785 := by
  unfold tailWord_6969516
  simp only [CollatzResearch.WordTrace]
  refine ⟨127099565909320652706700201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169466087879094203608933601 127099565909320652706700201)
  ·
    refine ⟨95324674431990489530025151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127099565909320652706700201 95324674431990489530025151)
    ·
      refine ⟨142987011647985734295037727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95324674431990489530025151 142987011647985734295037727)
      ·
        refine ⟨214480517471978601442556591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142987011647985734295037727 214480517471978601442556591)
        ·
          refine ⟨321720776207967902163834887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214480517471978601442556591 321720776207967902163834887)
          ·
            refine ⟨482581164311951853245752331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321720776207967902163834887 482581164311951853245752331)
            ·
              refine ⟨723871746467927779868628497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482581164311951853245752331 723871746467927779868628497)
              ·
                refine ⟨542903809850945834901471373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 723871746467927779868628497 542903809850945834901471373)
                ·
                  refine ⟨203588928694104688088051765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 542903809850945834901471373 203588928694104688088051765)
                  ·
                    refine ⟨19086462065072314508254853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 203588928694104688088051765 19086462065072314508254853)
                    ·
                      refine ⟨3578711637201058970297785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19086462065072314508254853 3578711637201058970297785)
                      ·
                        rfl

theorem cell23_6969516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_6969516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969516 prefixEnd_6969516 := by exact prefixLift 6969516
  have htrace : WordTrace (prefixWord ++ tailWord_6969516) baseStart_6969516 baseEnd_6969516 := by
    simpa [prefixWord, tailWord_6969516, baseEnd_6969516] using wordTrace_append hprefix tailTrace_6969516
  have hstable : (prefixWord ++ tailWord_6969516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969516).length < 2 ^ (prefixWord ++ tailWord_6969516).sum := by decide
  have hdescent : baseEnd_6969516 < baseStart_6969516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969571 : List Nat := [1, 1, 1, 8, 1, 2, 1, 2, 1, 3, 2]
def baseStart_6969571 : Nat := 118140960795 + 6969571 * 2 ^ 59
def prefixEnd_6969571 : Nat := 4983230072969 + 3 ^ 40 * 6969571 * 2
def baseEnd_6969571 : Nat := 3578739878637056255110033

theorem tailTrace_6969571 : CollatzResearch.WordTrace tailWord_6969571 prefixEnd_6969571 3578739878637056255110033 := by
  unfold tailWord_6969571
  simp only [CollatzResearch.WordTrace]
  refine ⟨254201137833442049806652567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169467425222294699871101711 254201137833442049806652567)
  ·
    refine ⟨381301706750163074709978851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254201137833442049806652567 381301706750163074709978851)
    ·
      refine ⟨571952560125244612064968277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381301706750163074709978851 571952560125244612064968277)
      ·
        refine ⟨6702569063967710297636347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 571952560125244612064968277 6702569063967710297636347)
        ·
          refine ⟨10053853595951565446454521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6702569063967710297636347 10053853595951565446454521)
          ·
            refine ⟨7540390196963674084840891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10053853595951565446454521 7540390196963674084840891)
            ·
              refine ⟨11310585295445511127261337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7540390196963674084840891 11310585295445511127261337)
              ·
                refine ⟨8482938971584133345446003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11310585295445511127261337 8482938971584133345446003)
                ·
                  refine ⟨12724408457376200018169005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8482938971584133345446003 12724408457376200018169005)
                  ·
                    refine ⟨4771653171516075006813377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12724408457376200018169005 4771653171516075006813377)
                    ·
                      refine ⟨3578739878637056255110033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4771653171516075006813377 3578739878637056255110033)
                      ·
                        rfl

theorem cell23_6969571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_6969571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969571 prefixEnd_6969571 := by exact prefixLift 6969571
  have htrace : WordTrace (prefixWord ++ tailWord_6969571) baseStart_6969571 baseEnd_6969571 := by
    simpa [prefixWord, tailWord_6969571, baseEnd_6969571] using wordTrace_append hprefix tailTrace_6969571
  have hstable : (prefixWord ++ tailWord_6969571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969571).length < 2 ^ (prefixWord ++ tailWord_6969571).sum := by decide
  have hdescent : baseEnd_6969571 < baseStart_6969571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969603 : List Nat := [1, 1, 1, 3, 2, 3, 1, 4, 2, 5]
def baseStart_6969603 : Nat := 118140960795 + 6969603 * 2 ^ 59
def prefixEnd_6969603 : Nat := 4983230072969 + 3 ^ 40 * 6969603 * 2
def baseEnd_6969603 : Nat := 1192918770006000043303295

theorem tailTrace_6969603 : CollatzResearch.WordTrace tailWord_6969603 prefixEnd_6969603 1192918770006000043303295 := by
  unfold tailWord_6969603
  simp only [CollatzResearch.WordTrace]
  refine ⟨254202304969326119271817463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169468203312884079514544975 254202304969326119271817463)
  ·
    refine ⟨381303457453989178907726195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254202304969326119271817463 381303457453989178907726195)
    ·
      refine ⟨571955186180983768361589293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381303457453989178907726195 571955186180983768361589293)
      ·
        refine ⟨214483194817868913135595985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 571955186180983768361589293 214483194817868913135595985)
        ·
          refine ⟨160862396113401684851696989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214483194817868913135595985 160862396113401684851696989)
          ·
            refine ⟨60323398542525631819386371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160862396113401684851696989 60323398542525631819386371)
            ·
              refine ⟨90485097813788447729079557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60323398542525631819386371 90485097813788447729079557)
              ·
                refine ⟨16965955840085333949202417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90485097813788447729079557 16965955840085333949202417)
                ·
                  refine ⟨12724466880064000461901813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16965955840085333949202417 12724466880064000461901813)
                  ·
                    refine ⟨1192918770006000043303295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12724466880064000461901813 1192918770006000043303295)
                    ·
                      rfl

theorem cell23_6969603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 5].length) (baseStart_6969603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969603 prefixEnd_6969603 := by exact prefixLift 6969603
  have htrace : WordTrace (prefixWord ++ tailWord_6969603) baseStart_6969603 baseEnd_6969603 := by
    simpa [prefixWord, tailWord_6969603, baseEnd_6969603] using wordTrace_append hprefix tailTrace_6969603
  have hstable : (prefixWord ++ tailWord_6969603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969603).length < 2 ^ (prefixWord ++ tailWord_6969603).sum := by decide
  have hdescent : baseEnd_6969603 < baseStart_6969603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969610 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2]
def baseStart_6969610 : Nat := 118140960795 + 6969610 * 2 ^ 59
def prefixEnd_6969610 : Nat := 4983230072969 + 3 ^ 40 * 6969610 * 2
def baseEnd_6969610 : Nat := 3578759904382581602522353

theorem tailTrace_6969610 : CollatzResearch.WordTrace tailWord_6969610 prefixEnd_6969610 3578759904382581602522353 := by
  unfold tailWord_6969610
  simp only [CollatzResearch.WordTrace]
  refine ⟨63550640070075189866830571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169468373520200506311548189 63550640070075189866830571)
  ·
    refine ⟨95325960105112784800245857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63550640070075189866830571 95325960105112784800245857)
    ·
      refine ⟨71494470078834588600184393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95325960105112784800245857 71494470078834588600184393)
      ·
        refine ⟨53620852559125941450138295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71494470078834588600184393 53620852559125941450138295)
        ·
          refine ⟨80431278838688912175207443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53620852559125941450138295 80431278838688912175207443)
          ·
            refine ⟨120646918258033368262811165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80431278838688912175207443 120646918258033368262811165)
            ·
              refine ⟨45242594346762513098554187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120646918258033368262811165 45242594346762513098554187)
              ·
                refine ⟨67863891520143769647831281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45242594346762513098554187 67863891520143769647831281)
                ·
                  refine ⟨50897918640107827235873461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67863891520143769647831281 50897918640107827235873461)
                  ·
                    refine ⟨4771679872510108803363137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50897918640107827235873461 4771679872510108803363137)
                    ·
                      refine ⟨3578759904382581602522353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4771679872510108803363137 3578759904382581602522353)
                      ·
                        rfl

theorem cell23_6969610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_6969610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969610 prefixEnd_6969610 := by exact prefixLift 6969610
  have htrace : WordTrace (prefixWord ++ tailWord_6969610) baseStart_6969610 baseEnd_6969610 := by
    simpa [prefixWord, tailWord_6969610, baseEnd_6969610] using wordTrace_append hprefix tailTrace_6969610
  have hstable : (prefixWord ++ tailWord_6969610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969610).length < 2 ^ (prefixWord ++ tailWord_6969610).sum := by decide
  have hdescent : baseEnd_6969610 < baseStart_6969610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969637 : List Nat := [1, 3, 1, 2, 5, 2, 1, 1, 2, 5]
def baseStart_6969637 : Nat := 118140960795 + 6969637 * 2 ^ 59
def prefixEnd_6969637 : Nat := 4983230072969 + 3 ^ 40 * 6969637 * 2
def baseEnd_6969637 : Nat := 1192924589453417665628243

theorem tailTrace_6969637 : CollatzResearch.WordTrace tailWord_6969637 prefixEnd_6969637 1192924589453417665628243 := by
  unfold tailWord_6969637
  simp only [CollatzResearch.WordTrace]
  refine ⟨254203545051202943078555165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169469030034135295385703443 254203545051202943078555165)
  ·
    refine ⟨95326329394201103654458187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254203545051202943078555165 95326329394201103654458187)
    ·
      refine ⟨142989494091301655481687281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95326329394201103654458187 142989494091301655481687281)
      ·
        refine ⟨107242120568476241611265461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142989494091301655481687281 107242120568476241611265461)
        ·
          refine ⟨10053948803294647651056137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107242120568476241611265461 10053948803294647651056137)
          ·
            refine ⟨7540461602470985738292103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10053948803294647651056137 7540461602470985738292103)
            ·
              refine ⟨11310692403706478607438155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7540461602470985738292103 11310692403706478607438155)
              ·
                refine ⟨16966038605559717911157233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11310692403706478607438155 16966038605559717911157233)
                ·
                  refine ⟨12724528954169788433367925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16966038605559717911157233 12724528954169788433367925)
                  ·
                    refine ⟨1192924589453417665628243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12724528954169788433367925 1192924589453417665628243)
                    ·
                      rfl

theorem cell23_6969637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 5].length) (baseStart_6969637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969637 prefixEnd_6969637 := by exact prefixLift 6969637
  have htrace : WordTrace (prefixWord ++ tailWord_6969637) baseStart_6969637 baseEnd_6969637 := by
    simpa [prefixWord, tailWord_6969637, baseEnd_6969637] using wordTrace_append hprefix tailTrace_6969637
  have hstable : (prefixWord ++ tailWord_6969637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969637).length < 2 ^ (prefixWord ++ tailWord_6969637).sum := by decide
  have hdescent : baseEnd_6969637 < baseStart_6969637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969653 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 1, 3, 6]
def baseStart_6969653 : Nat := 118140960795 + 6969653 * 2 ^ 59
def prefixEnd_6969653 : Nat := 4983230072969 + 3 ^ 40 * 6969653 * 2
def baseEnd_6969653 : Nat := 3578781984050724934284655

theorem tailTrace_6969653 : CollatzResearch.WordTrace tailWord_6969653 prefixEnd_6969653 3578781984050724934284655 := by
  unfold tailWord_6969653
  simp only [CollatzResearch.WordTrace]
  refine ⟨254204128619144977811137613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169469419079429985207425075 254204128619144977811137613)
  ·
    refine ⟨95326548232179366679176605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254204128619144977811137613 95326548232179366679176605)
    ·
      refine ⟨35747455587067262504691227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95326548232179366679176605 35747455587067262504691227)
      ·
        refine ⟨53621183380600893757036841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35747455587067262504691227 53621183380600893757036841)
        ·
          refine ⟨40215887535450670317777631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53621183380600893757036841 40215887535450670317777631)
          ·
            refine ⟨60323831303176005476666447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40215887535450670317777631 60323831303176005476666447)
            ·
              refine ⟨90485746954764008214999671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60323831303176005476666447 90485746954764008214999671)
              ·
                refine ⟨135728620432146012322499507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90485746954764008214999671 135728620432146012322499507)
                ·
                  refine ⟨203592930648219018483749261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135728620432146012322499507 203592930648219018483749261)
                  ·
                    refine ⟨76347348993082131931405973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 203592930648219018483749261 76347348993082131931405973)
                    ·
                      refine ⟨3578781984050724934284655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76347348993082131931405973 3578781984050724934284655)
                      ·
                        rfl

theorem cell23_6969653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_6969653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969653 prefixEnd_6969653 := by exact prefixLift 6969653
  have htrace : WordTrace (prefixWord ++ tailWord_6969653) baseStart_6969653 baseEnd_6969653 := by
    simpa [prefixWord, tailWord_6969653, baseEnd_6969653] using wordTrace_append hprefix tailTrace_6969653
  have hstable : (prefixWord ++ tailWord_6969653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969653).length < 2 ^ (prefixWord ++ tailWord_6969653).sum := by decide
  have hdescent : baseEnd_6969653 < baseStart_6969653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969657 : List Nat := [1, 2, 1, 6, 1, 1, 1, 2, 2, 4, 2]
def baseStart_6969657 : Nat := 118140960795 + 6969657 * 2 ^ 59
def prefixEnd_6969657 : Nat := 4983230072969 + 3 ^ 40 * 6969657 * 2
def baseEnd_6969657 : Nat := 3578784037973342918634637

theorem tailTrace_6969657 : CollatzResearch.WordTrace tailWord_6969657 prefixEnd_6969657 3578784037973342918634637 := by
  unfold tailWord_6969657
  simp only [CollatzResearch.WordTrace]
  refine ⟨254204274511130486494283225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169469516340753657662855483 254204274511130486494283225)
  ·
    refine ⟨190653205883347864870712419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254204274511130486494283225 190653205883347864870712419)
    ·
      refine ⟨285979808825021797306068629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190653205883347864870712419 285979808825021797306068629)
      ·
        refine ⟨13405303538672896748721967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 285979808825021797306068629 13405303538672896748721967)
        ·
          refine ⟨20107955308009345123082951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13405303538672896748721967 20107955308009345123082951)
          ·
            refine ⟨30161932962014017684624427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20107955308009345123082951 30161932962014017684624427)
            ·
              refine ⟨45242899443021026526936641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30161932962014017684624427 45242899443021026526936641)
              ·
                refine ⟨33932174582265769895202481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45242899443021026526936641 33932174582265769895202481)
                ·
                  refine ⟨25449130936699327421401861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33932174582265769895202481 25449130936699327421401861)
                  ·
                    refine ⟨4771712050631123891512849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25449130936699327421401861 4771712050631123891512849)
                    ·
                      refine ⟨3578784037973342918634637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4771712050631123891512849 3578784037973342918634637)
                      ·
                        rfl

theorem cell23_6969657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_6969657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969657 prefixEnd_6969657 := by exact prefixLift 6969657
  have htrace : WordTrace (prefixWord ++ tailWord_6969657) baseStart_6969657 baseEnd_6969657 := by
    simpa [prefixWord, tailWord_6969657, baseEnd_6969657] using wordTrace_append hprefix tailTrace_6969657
  have hstable : (prefixWord ++ tailWord_6969657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969657).length < 2 ^ (prefixWord ++ tailWord_6969657).sum := by decide
  have hdescent : baseEnd_6969657 < baseStart_6969657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969660 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 4, 2, 3]
def baseStart_6969660 : Nat := 118140960795 + 6969660 * 2 ^ 59
def prefixEnd_6969660 : Nat := 4983230072969 + 3 ^ 40 * 6969660 * 2
def baseEnd_6969660 : Nat := 3578785578415306406897123

theorem tailTrace_6969660 : CollatzResearch.WordTrace tailWord_6969660 prefixEnd_6969660 3578785578415306406897123 := by
  unfold tailWord_6969660
  simp only [CollatzResearch.WordTrace]
  refine ⟨127102191965059809003321217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169469589286746412004428289 127102191965059809003321217)
  ·
    refine ⟨95326643973794856752490913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127102191965059809003321217 95326643973794856752490913)
    ·
      refine ⟨71494982980346142564368185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95326643973794856752490913 71494982980346142564368185)
      ·
        refine ⟨53621237235259606923276139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71494982980346142564368185 53621237235259606923276139)
        ·
          refine ⟨80431855852889410384914209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53621237235259606923276139 80431855852889410384914209)
          ·
            refine ⟨60323891889667057788685657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80431855852889410384914209 60323891889667057788685657)
            ·
              refine ⟨45242918917250293341514243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60323891889667057788685657 45242918917250293341514243)
              ·
                refine ⟨67864378375875440012271365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45242918917250293341514243 67864378375875440012271365)
                ·
                  refine ⟨12724570945476645002300881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67864378375875440012271365 12724570945476645002300881)
                  ·
                    refine ⟨9543428209107483751725661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12724570945476645002300881 9543428209107483751725661)
                    ·
                      refine ⟨3578785578415306406897123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9543428209107483751725661 3578785578415306406897123)
                      ·
                        rfl

theorem cell23_6969660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_6969660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969660 prefixEnd_6969660 := by exact prefixLift 6969660
  have htrace : WordTrace (prefixWord ++ tailWord_6969660) baseStart_6969660 baseEnd_6969660 := by
    simpa [prefixWord, tailWord_6969660, baseEnd_6969660] using wordTrace_append hprefix tailTrace_6969660
  have hstable : (prefixWord ++ tailWord_6969660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969660).length < 2 ^ (prefixWord ++ tailWord_6969660).sum := by decide
  have hdescent : baseEnd_6969660 < baseStart_6969660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969663 : List Nat := [1, 1, 2, 2, 4, 1, 3, 1, 8]
def baseStart_6969663 : Nat := 118140960795 + 6969663 * 2 ^ 59
def prefixEnd_6969663 : Nat := 4983230072969 + 3 ^ 40 * 6969663 * 2
def baseEnd_6969663 : Nat := 397643013206363321684401

theorem tailTrace_6969663 : CollatzResearch.WordTrace tailWord_6969663 prefixEnd_6969663 397643013206363321684401 := by
  unfold tailWord_6969663
  simp only [CollatzResearch.WordTrace]
  refine ⟨254204493349108749519001643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169469662232739166346001095 254204493349108749519001643)
  ·
    refine ⟨381306740023663124278502465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254204493349108749519001643 381306740023663124278502465)
    ·
      refine ⟨285980055017747343208876849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381306740023663124278502465 285980055017747343208876849)
      ·
        refine ⟨214485041263310507406657637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285980055017747343208876849 214485041263310507406657637)
        ·
          refine ⟨40215945236870720138748307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214485041263310507406657637 40215945236870720138748307)
          ·
            refine ⟨60323917855306080208122461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40215945236870720138748307 60323917855306080208122461)
            ·
              refine ⟨22621469195739780078045923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60323917855306080208122461 22621469195739780078045923)
              ·
                refine ⟨33932203793609670117068885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22621469195739780078045923 33932203793609670117068885)
                ·
                  refine ⟨397643013206363321684401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33932203793609670117068885 397643013206363321684401)
                  ·
                    rfl

theorem cell23_6969663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 8].length) (baseStart_6969663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969663 prefixEnd_6969663 := by exact prefixLift 6969663
  have htrace : WordTrace (prefixWord ++ tailWord_6969663) baseStart_6969663 baseEnd_6969663 := by
    simpa [prefixWord, tailWord_6969663, baseEnd_6969663] using wordTrace_append hprefix tailTrace_6969663
  have hstable : (prefixWord ++ tailWord_6969663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969663).length < 2 ^ (prefixWord ++ tailWord_6969663).sum := by decide
  have hdescent : baseEnd_6969663 < baseStart_6969663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969667 : List Nat := [1, 1, 1, 3, 1, 3, 4, 4, 1, 4]
def baseStart_6969667 : Nat := 118140960795 + 6969667 * 2 ^ 59
def prefixEnd_6969667 : Nat := 4983230072969 + 3 ^ 40 * 6969667 * 2
def baseEnd_6969667 : Nat := 1192929724259962626503197

theorem tailTrace_6969667 : CollatzResearch.WordTrace tailWord_6969667 prefixEnd_6969667 1192929724259962626503197 := by
  unfold tailWord_6969667
  simp only [CollatzResearch.WordTrace]
  refine ⟨254204639241094258202147255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169469759494062838801431503 254204639241094258202147255)
  ·
    refine ⟨381306958861641387303220883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254204639241094258202147255 381306958861641387303220883)
    ·
      refine ⟨571960438292462080954831325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381306958861641387303220883 571960438292462080954831325)
      ·
        refine ⟨214485164359673280358061747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 571960438292462080954831325 214485164359673280358061747)
        ·
          refine ⟨321727746539509920537092621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214485164359673280358061747 321727746539509920537092621)
          ·
            refine ⟨120647904952316220201409733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 321727746539509920537092621 120647904952316220201409733)
            ·
              refine ⟨22621482178559291287764325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120647904952316220201409733 22621482178559291287764325)
              ·
                refine ⟨4241527908479867116455811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22621482178559291287764325 4241527908479867116455811)
                ·
                  refine ⟨6362291862719800674683717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4241527908479867116455811 6362291862719800674683717)
                  ·
                    refine ⟨1192929724259962626503197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6362291862719800674683717 1192929724259962626503197)
                    ·
                      rfl

theorem cell23_6969667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4, 1, 4].length) (baseStart_6969667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969667 prefixEnd_6969667 := by exact prefixLift 6969667
  have htrace : WordTrace (prefixWord ++ tailWord_6969667) baseStart_6969667 baseEnd_6969667 := by
    simpa [prefixWord, tailWord_6969667, baseEnd_6969667] using wordTrace_append hprefix tailTrace_6969667
  have hstable : (prefixWord ++ tailWord_6969667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969667).length < 2 ^ (prefixWord ++ tailWord_6969667).sum := by decide
  have hdescent : baseEnd_6969667 < baseStart_6969667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969718 : List Nat := [5, 1, 1, 4, 2, 1, 1, 1, 3, 4]
def baseStart_6969718 : Nat := 118140960795 + 6969718 * 2 ^ 59
def prefixEnd_6969718 : Nat := 4983230072969 + 3 ^ 40 * 6969718 * 2
def baseEnd_6969718 : Nat := 1192938453431089059990619

theorem tailTrace_6969718 : CollatzResearch.WordTrace tailWord_6969718 prefixEnd_6969718 1192938453431089059990619 := by
  unfold tailWord_6969718
  simp only [CollatzResearch.WordTrace]
  refine ⟨15887906210244343369515863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169470999575939662608169205 15887906210244343369515863)
  ·
    refine ⟨23831859315366515054273795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15887906210244343369515863 23831859315366515054273795)
    ·
      refine ⟨35747788973049772581410693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23831859315366515054273795 35747788973049772581410693)
      ·
        refine ⟨6702710432446832359014505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35747788973049772581410693 6702710432446832359014505)
        ·
          refine ⟨5027032824335124269260879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6702710432446832359014505 5027032824335124269260879)
          ·
            refine ⟨7540549236502686403891319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5027032824335124269260879 7540549236502686403891319)
            ·
              refine ⟨11310823854754029605836979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7540549236502686403891319 11310823854754029605836979)
              ·
                refine ⟨16966235782131044408755469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11310823854754029605836979 16966235782131044408755469)
                ·
                  refine ⟨6362338418299141653283301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16966235782131044408755469 6362338418299141653283301)
                  ·
                    refine ⟨1192938453431089059990619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6362338418299141653283301 1192938453431089059990619)
                    ·
                      rfl

theorem cell23_6969718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_6969718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969718 prefixEnd_6969718 := by exact prefixLift 6969718
  have htrace : WordTrace (prefixWord ++ tailWord_6969718) baseStart_6969718 baseEnd_6969718 := by
    simpa [prefixWord, tailWord_6969718, baseEnd_6969718] using wordTrace_append hprefix tailTrace_6969718
  have hstable : (prefixWord ++ tailWord_6969718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969718).length < 2 ^ (prefixWord ++ tailWord_6969718).sum := by decide
  have hdescent : baseEnd_6969718 < baseStart_6969718 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969753 : List Nat := [1, 2, 1, 2, 1, 4, 1, 11]
def baseStart_6969753 : Nat := 118140960795 + 6969753 * 2 ^ 59
def prefixEnd_6969753 : Nat := 4983230072969 + 3 ^ 40 * 6969753 * 2
def baseEnd_6969753 : Nat := 132549382670969427519785

theorem tailTrace_6969753 : CollatzResearch.WordTrace tailWord_6969753 prefixEnd_6969753 132549382670969427519785 := by
  unfold tailWord_6969753
  simp only [CollatzResearch.WordTrace]
  refine ⟨254207775918782694889777913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169471850612521796593185275 254207775918782694889777913)
  ·
    refine ⟨190655831939087021167333435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254207775918782694889777913 190655831939087021167333435)
    ·
      refine ⟨285983747908630531751000153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190655831939087021167333435 285983747908630531751000153)
      ·
        refine ⟨214487810931472898813250115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285983747908630531751000153 214487810931472898813250115)
        ·
          refine ⟨321731716397209348219875173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214487810931472898813250115 321731716397209348219875173)
          ·
            refine ⟨60324696824476752791226595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 321731716397209348219875173 60324696824476752791226595)
            ·
              refine ⟨90487045236715129186839893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60324696824476752791226595 90487045236715129186839893)
              ·
                refine ⟨132549382670969427519785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 90487045236715129186839893 132549382670969427519785)
                ·
                  rfl

theorem cell23_6969753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 11].length) (baseStart_6969753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969753 prefixEnd_6969753 := by exact prefixLift 6969753
  have htrace : WordTrace (prefixWord ++ tailWord_6969753) baseStart_6969753 baseEnd_6969753 := by
    simpa [prefixWord, tailWord_6969753, baseEnd_6969753] using wordTrace_append hprefix tailTrace_6969753
  have hstable : (prefixWord ++ tailWord_6969753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969753).length < 2 ^ (prefixWord ++ tailWord_6969753).sum := by decide
  have hdescent : baseEnd_6969753 < baseStart_6969753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969757 : List Nat := [1, 4, 2, 1, 4, 1, 1, 2, 1, 6]
def baseStart_6969757 : Nat := 118140960795 + 6969757 * 2 ^ 59
def prefixEnd_6969757 : Nat := 4983230072969 + 3 ^ 40 * 6969757 * 2
def baseEnd_6969757 : Nat := 1192945128679597509128059

theorem tailTrace_6969757 : CollatzResearch.WordTrace tailWord_6969757 prefixEnd_6969757 1192945128679597509128059 := by
  unfold tailWord_6969757
  simp only [CollatzResearch.WordTrace]
  refine ⟨254207921810768203572923525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169471947873845469048615683 254207921810768203572923525)
  ·
    refine ⟨47663985339519038169923161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254207921810768203572923525 47663985339519038169923161)
    ·
      refine ⟨35747989004639278627442371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47663985339519038169923161 35747989004639278627442371)
      ·
        refine ⟨53621983506958917941163557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35747989004639278627442371 53621983506958917941163557)
        ·
          refine ⟨10054121907554797113968167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53621983506958917941163557 10054121907554797113968167)
          ·
            refine ⟨15081182861332195670952251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10054121907554797113968167 15081182861332195670952251)
            ·
              refine ⟨22621774291998293506428377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15081182861332195670952251 22621774291998293506428377)
              ·
                refine ⟨16966330718998720129821283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22621774291998293506428377 16966330718998720129821283)
                ·
                  refine ⟨25449496078498080194731925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16966330718998720129821283 25449496078498080194731925)
                  ·
                    refine ⟨1192945128679597509128059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25449496078498080194731925 1192945128679597509128059)
                    ·
                      rfl

theorem cell23_6969757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_6969757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969757 prefixEnd_6969757 := by exact prefixLift 6969757
  have htrace : WordTrace (prefixWord ++ tailWord_6969757) baseStart_6969757 baseEnd_6969757 := by
    simpa [prefixWord, tailWord_6969757, baseEnd_6969757] using wordTrace_append hprefix tailTrace_6969757
  have hstable : (prefixWord ++ tailWord_6969757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969757).length < 2 ^ (prefixWord ++ tailWord_6969757).sum := by decide
  have hdescent : baseEnd_6969757 < baseStart_6969757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969760 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 4]
def baseStart_6969760 : Nat := 118140960795 + 6969760 * 2 ^ 59
def prefixEnd_6969760 : Nat := 4983230072969 + 3 ^ 40 * 6969760 * 2
def baseEnd_6969760 : Nat := 3578836926480756015646663

theorem tailTrace_6969760 : CollatzResearch.WordTrace tailWord_6969760 prefixEnd_6969760 3578836926480756015646663 := by
  unfold tailWord_6969760
  simp only [CollatzResearch.WordTrace]
  refine ⟨127104015614878667542641367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169472020819838223390188489 127104015614878667542641367)
  ·
    refine ⟨190656023422318001313962051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127104015614878667542641367 190656023422318001313962051)
    ·
      refine ⟨285984035133477001970943077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190656023422318001313962051 285984035133477001970943077)
      ·
        refine ⟨53622006587526937869551827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 285984035133477001970943077 53622006587526937869551827)
        ·
          refine ⟨80433009881290406804327741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53622006587526937869551827 80433009881290406804327741)
          ·
            refine ⟨30162378705483902551622903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80433009881290406804327741 30162378705483902551622903)
            ·
              refine ⟨45243568058225853827434355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30162378705483902551622903 45243568058225853827434355)
              ·
                refine ⟨67865352087338780741151533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45243568058225853827434355 67865352087338780741151533)
                ·
                  refine ⟨25449507032752042777931825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67865352087338780741151533 25449507032752042777931825)
                  ·
                    refine ⟨19087130274564032083448869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25449507032752042777931825 19087130274564032083448869)
                    ·
                      refine ⟨3578836926480756015646663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19087130274564032083448869 3578836926480756015646663)
                      ·
                        rfl

theorem cell23_6969760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_6969760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969760 prefixEnd_6969760 := by exact prefixLift 6969760
  have htrace : WordTrace (prefixWord ++ tailWord_6969760) baseStart_6969760 baseEnd_6969760 := by
    simpa [prefixWord, tailWord_6969760, baseEnd_6969760] using wordTrace_append hprefix tailTrace_6969760
  have hstable : (prefixWord ++ tailWord_6969760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969760).length < 2 ^ (prefixWord ++ tailWord_6969760).sum := by decide
  have hdescent : baseEnd_6969760 < baseStart_6969760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969761 : List Nat := [1, 2, 3, 5, 1, 1, 3, 1, 1, 5]
def baseStart_6969761 : Nat := 118140960795 + 6969761 * 2 ^ 59
def prefixEnd_6969761 : Nat := 4983230072969 + 3 ^ 40 * 6969761 * 2
def baseEnd_6969761 : Nat := 1192945813320470170578053

theorem tailTrace_6969761 : CollatzResearch.WordTrace tailWord_6969761 prefixEnd_6969761 1192945813320470170578053 := by
  unfold tailWord_6969761
  simp only [CollatzResearch.WordTrace]
  refine ⟨254208067702753712256069137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169472045135169141504046091 254208067702753712256069137)
  ·
    refine ⟨190656050777065284192051853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254208067702753712256069137 190656050777065284192051853)
    ·
      refine ⟨71496019041399481572019445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190656050777065284192051853 71496019041399481572019445)
      ·
        refine ⟨6702751785131201397376823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71496019041399481572019445 6702751785131201397376823)
        ·
          refine ⟨10054127677696802096065235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6702751785131201397376823 10054127677696802096065235)
          ·
            refine ⟨15081191516545203144097853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10054127677696802096065235 15081191516545203144097853)
            ·
              refine ⟨5655446818704451179036695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15081191516545203144097853 5655446818704451179036695)
              ·
                refine ⟨8483170228056676768555043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5655446818704451179036695 8483170228056676768555043)
                ·
                  refine ⟨12724755342085015152832565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8483170228056676768555043 12724755342085015152832565)
                  ·
                    refine ⟨1192945813320470170578053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12724755342085015152832565 1192945813320470170578053)
                    ·
                      rfl

theorem cell23_6969761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_6969761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969761 prefixEnd_6969761 := by exact prefixLift 6969761
  have htrace : WordTrace (prefixWord ++ tailWord_6969761) baseStart_6969761 baseEnd_6969761 := by
    simpa [prefixWord, tailWord_6969761, baseEnd_6969761] using wordTrace_append hprefix tailTrace_6969761
  have hstable : (prefixWord ++ tailWord_6969761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969761).length < 2 ^ (prefixWord ++ tailWord_6969761).sum := by decide
  have hdescent : baseEnd_6969761 < baseStart_6969761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969767 : List Nat := [1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 5]
def baseStart_6969767 : Nat := 118140960795 + 6969767 * 2 ^ 59
def prefixEnd_6969767 : Nat := 4983230072969 + 3 ^ 40 * 6969767 * 2
def baseEnd_6969767 : Nat := 3578840520845337488259131

theorem tailTrace_6969767 : CollatzResearch.WordTrace tailWord_6969767 prefixEnd_6969767 3578840520845337488259131 := by
  unfold tailWord_6969767
  simp only [CollatzResearch.WordTrace]
  refine ⟨254208286540731975280787555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169472191027154650187191703 254208286540731975280787555)
  ·
    refine ⟨381312429811097962921181333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254208286540731975280787555 381312429811097962921181333)
    ·
      refine ⟨17874020147395217011930375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 381312429811097962921181333 17874020147395217011930375)
      ·
        refine ⟨26811030221092825517895563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17874020147395217011930375 26811030221092825517895563)
        ·
          refine ⟨40216545331639238276843345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26811030221092825517895563 40216545331639238276843345)
          ·
            refine ⟨30162408998729428707632509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40216545331639238276843345 30162408998729428707632509)
            ·
              refine ⟨11310903374523535765362191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30162408998729428707632509 11310903374523535765362191)
              ·
                refine ⟨16966355061785303648043287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11310903374523535765362191 16966355061785303648043287)
                ·
                  refine ⟨25449532592677955472064931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16966355061785303648043287 25449532592677955472064931)
                  ·
                    refine ⟨38174298889016933208097397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25449532592677955472064931 38174298889016933208097397)
                    ·
                      refine ⟨3578840520845337488259131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38174298889016933208097397 3578840520845337488259131)
                      ·
                        rfl

theorem cell23_6969767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_6969767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969767 prefixEnd_6969767 := by exact prefixLift 6969767
  have htrace : WordTrace (prefixWord ++ tailWord_6969767) baseStart_6969767 baseEnd_6969767 := by
    simpa [prefixWord, tailWord_6969767, baseEnd_6969767] using wordTrace_append hprefix tailTrace_6969767
  have hstable : (prefixWord ++ tailWord_6969767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969767).length < 2 ^ (prefixWord ++ tailWord_6969767).sum := by decide
  have hdescent : baseEnd_6969767 < baseStart_6969767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969790 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6]
def baseStart_6969790 : Nat := 118140960795 + 6969790 * 2 ^ 59
def prefixEnd_6969790 : Nat := 4983230072969 + 3 ^ 40 * 6969790 * 2
def baseEnd_6969790 : Nat := 3578852330900390898271525

theorem tailTrace_6969790 : CollatzResearch.WordTrace tailWord_6969790 prefixEnd_6969790 3578852330900390898271525 := by
  unfold tailWord_6969790
  simp only [CollatzResearch.WordTrace]
  refine ⟨31776140677456081276109353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169472750279765766805916549 31776140677456081276109353)
  ·
    refine ⟨23832105508092060957082015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31776140677456081276109353 23832105508092060957082015)
    ·
      refine ⟨35748158262138091435623023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23832105508092060957082015 35748158262138091435623023)
      ·
        refine ⟨53622237393207137153434535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35748158262138091435623023 53622237393207137153434535)
        ·
          refine ⟨80433356089810705730151803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53622237393207137153434535 80433356089810705730151803)
          ·
            refine ⟨120650034134716058595227705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80433356089810705730151803 120650034134716058595227705)
            ·
              refine ⟨90487525601037043946420779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120650034134716058595227705 90487525601037043946420779)
              ·
                refine ⟨135731288401555565919631169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90487525601037043946420779 135731288401555565919631169)
                ·
                  refine ⟨101798466301166674439723377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135731288401555565919631169 101798466301166674439723377)
                  ·
                    refine ⟨76348849725875005829792533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101798466301166674439723377 76348849725875005829792533)
                    ·
                      refine ⟨3578852330900390898271525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76348849725875005829792533 3578852330900390898271525)
                      ·
                        rfl

theorem cell23_6969790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_6969790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969790 prefixEnd_6969790 := by exact prefixLift 6969790
  have htrace : WordTrace (prefixWord ++ tailWord_6969790) baseStart_6969790 baseEnd_6969790 := by
    simpa [prefixWord, tailWord_6969790, baseEnd_6969790] using wordTrace_append hprefix tailTrace_6969790
  have hstable : (prefixWord ++ tailWord_6969790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969790).length < 2 ^ (prefixWord ++ tailWord_6969790).sum := by decide
  have hdescent : baseEnd_6969790 < baseStart_6969790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969814 : List Nat := [5, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3]
def baseStart_6969814 : Nat := 118140960795 + 6969814 * 2 ^ 59
def prefixEnd_6969814 : Nat := 4983230072969 + 3 ^ 40 * 6969814 * 2
def baseEnd_6969814 : Nat := 3578864654436098804371415

theorem tailTrace_6969814 : CollatzResearch.WordTrace tailWord_6969814 prefixEnd_6969814 3578864654436098804371415 := by
  unfold tailWord_6969814
  simp only [CollatzResearch.WordTrace]
  refine ⟨15888125048222606394234281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169473333847707801538498997 15888125048222606394234281)
  ·
    refine ⟨11916093786166954795675711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15888125048222606394234281 11916093786166954795675711)
    ·
      refine ⟨17874140679250432193513567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11916093786166954795675711 17874140679250432193513567)
      ·
        refine ⟨26811211018875648290270351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17874140679250432193513567 26811211018875648290270351)
        ·
          refine ⟨40216816528313472435405527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26811211018875648290270351 40216816528313472435405527)
          ·
            refine ⟨60325224792470208653108291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40216816528313472435405527 60325224792470208653108291)
            ·
              refine ⟨90487837188705312979662437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60325224792470208653108291 90487837188705312979662437)
              ·
                refine ⟨16966469472882246183686707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90487837188705312979662437 16966469472882246183686707)
                ·
                  refine ⟨25449704209323369275530061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16966469472882246183686707 25449704209323369275530061)
                  ·
                    refine ⟨9543639078496263478323773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25449704209323369275530061 9543639078496263478323773)
                    ·
                      refine ⟨3578864654436098804371415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9543639078496263478323773 3578864654436098804371415)
                      ·
                        rfl

theorem cell23_6969814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_6969814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969814 prefixEnd_6969814 := by exact prefixLift 6969814
  have htrace : WordTrace (prefixWord ++ tailWord_6969814) baseStart_6969814 baseEnd_6969814 := by
    simpa [prefixWord, tailWord_6969814, baseEnd_6969814] using wordTrace_append hprefix tailTrace_6969814
  have hstable : (prefixWord ++ tailWord_6969814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969814).length < 2 ^ (prefixWord ++ tailWord_6969814).sum := by decide
  have hdescent : baseEnd_6969814 < baseStart_6969814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969824 : List Nat := [2, 1, 1, 3, 1, 1, 5, 3, 1, 3, 2]
def baseStart_6969824 : Nat := 118140960795 + 6969824 * 2 ^ 59
def prefixEnd_6969824 : Nat := 4983230072969 + 3 ^ 40 * 6969824 * 2
def baseEnd_6969824 : Nat := 3578869789242643765246369

theorem tailTrace_6969824 : CollatzResearch.WordTrace tailWord_6969824 prefixEnd_6969824 3578869789242643765246369 := by
  unfold tailWord_6969824
  simp only [CollatzResearch.WordTrace]
  refine ⟨127105182750762737007806263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169473577001016982677075017 127105182750762737007806263)
  ·
    refine ⟨190657774126144105511709395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127105182750762737007806263 190657774126144105511709395)
    ·
      refine ⟨285986661189216158267564093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190657774126144105511709395 285986661189216158267564093)
      ·
        refine ⟨107244997945956059350336535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285986661189216158267564093 107244997945956059350336535)
        ·
          refine ⟨160867496918934089025504803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107244997945956059350336535 160867496918934089025504803)
          ·
            refine ⟨241301245378401133538257205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160867496918934089025504803 241301245378401133538257205)
            ·
              refine ⟨22621991754225106269211613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 241301245378401133538257205 22621991754225106269211613)
              ·
                refine ⟨8483246907834414850954355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22621991754225106269211613 8483246907834414850954355)
                ·
                  refine ⟨12724870361751622276431533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8483246907834414850954355 12724870361751622276431533)
                  ·
                    refine ⟨4771826385656858353661825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12724870361751622276431533 4771826385656858353661825)
                    ·
                      refine ⟨3578869789242643765246369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4771826385656858353661825 3578869789242643765246369)
                      ·
                        rfl

theorem cell23_6969824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 1, 3, 2].length) (baseStart_6969824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969824 prefixEnd_6969824 := by exact prefixLift 6969824
  have htrace : WordTrace (prefixWord ++ tailWord_6969824) baseStart_6969824 baseEnd_6969824 := by
    simpa [prefixWord, tailWord_6969824, baseEnd_6969824] using wordTrace_append hprefix tailTrace_6969824
  have hstable : (prefixWord ++ tailWord_6969824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969824).length < 2 ^ (prefixWord ++ tailWord_6969824).sum := by decide
  have hdescent : baseEnd_6969824 < baseStart_6969824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969850 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 1, 4, 4]
def baseStart_6969850 : Nat := 118140960795 + 6969850 * 2 ^ 59
def prefixEnd_6969850 : Nat := 4983230072969 + 3 ^ 40 * 6969850 * 2
def baseEnd_6969850 : Nat := 3578883139739660663521249

theorem tailTrace_6969850 : CollatzResearch.WordTrace tailWord_6969850 prefixEnd_6969850 3578883139739660663521249 := by
  unfold tailWord_6969850
  simp only [CollatzResearch.WordTrace]
  refine ⟨63552828449857820114014751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169474209199620853637372669 63552828449857820114014751)
  ·
    refine ⟨95329242674786730171022127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63552828449857820114014751 95329242674786730171022127)
    ·
      refine ⟨142993864012180095256533191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95329242674786730171022127 142993864012180095256533191)
      ·
        refine ⟨214490796018270142884799787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142993864012180095256533191 214490796018270142884799787)
        ·
          refine ⟨321736194027405214327199681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214490796018270142884799787 321736194027405214327199681)
          ·
            refine ⟨241302145520553910745399761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321736194027405214327199681 241302145520553910745399761)
            ·
              refine ⟨180976609140415433059049821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241302145520553910745399761 180976609140415433059049821)
              ·
                refine ⟨67866228427655787397143683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180976609140415433059049821 67866228427655787397143683)
                ·
                  refine ⟨101799342641483681095715525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67866228427655787397143683 101799342641483681095715525)
                  ·
                    refine ⟨19087376745278190205446661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101799342641483681095715525 19087376745278190205446661)
                    ·
                      refine ⟨3578883139739660663521249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19087376745278190205446661 3578883139739660663521249)
                      ·
                        rfl

theorem cell23_6969850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_6969850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969850 prefixEnd_6969850 := by exact prefixLift 6969850
  have htrace : WordTrace (prefixWord ++ tailWord_6969850) baseStart_6969850 baseEnd_6969850 := by
    simpa [prefixWord, tailWord_6969850, baseEnd_6969850] using wordTrace_append hprefix tailTrace_6969850
  have hstable : (prefixWord ++ tailWord_6969850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969850).length < 2 ^ (prefixWord ++ tailWord_6969850).sum := by decide
  have hdescent : baseEnd_6969850 < baseStart_6969850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969920 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 2, 8]
def baseStart_6969920 : Nat := 118140960795 + 6969920 * 2 ^ 59
def prefixEnd_6969920 : Nat := 4983230072969 + 3 ^ 40 * 6969920 * 2
def baseEnd_6969920 : Nat := 1192973027795158463215309

theorem tailTrace_6969920 : CollatzResearch.WordTrace tailWord_6969920 prefixEnd_6969920 1192973027795158463215309 := by
  unfold tailWord_6969920
  simp only [CollatzResearch.WordTrace]
  refine ⟨127106933454588841205553607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169475911272785121607404809 127106933454588841205553607)
  ·
    refine ⟨190660400181883261808330411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127106933454588841205553607 190660400181883261808330411)
    ·
      refine ⟨285990600272824892712495617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190660400181883261808330411 285990600272824892712495617)
      ·
        refine ⟨214492950204618669534371713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285990600272824892712495617 214492950204618669534371713)
        ·
          refine ⟨160869712653464002150778785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214492950204618669534371713 160869712653464002150778785)
          ·
            refine ⟨120652284490098001613084089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160869712653464002150778785 120652284490098001613084089)
            ·
              refine ⟨90489213367573501209813067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120652284490098001613084089 90489213367573501209813067)
              ·
                refine ⟨135733820051360251814719601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90489213367573501209813067 135733820051360251814719601)
                ·
                  refine ⟨101800365038520188861039701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135733820051360251814719601 101800365038520188861039701)
                  ·
                    refine ⟨1192973027795158463215309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101800365038520188861039701 1192973027795158463215309)
                    ·
                      rfl

theorem cell23_6969920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 8].length) (baseStart_6969920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969920 prefixEnd_6969920 := by exact prefixLift 6969920
  have htrace : WordTrace (prefixWord ++ tailWord_6969920) baseStart_6969920 baseEnd_6969920 := by
    simpa [prefixWord, tailWord_6969920, baseEnd_6969920] using wordTrace_append hprefix tailTrace_6969920
  have hstable : (prefixWord ++ tailWord_6969920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969920).length < 2 ^ (prefixWord ++ tailWord_6969920).sum := by decide
  have hdescent : baseEnd_6969920 < baseStart_6969920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969967 : List Nat := [1, 1, 2, 1, 3, 2, 4, 3, 6]
def baseStart_6969967 : Nat := 118140960795 + 6969967 * 2 ^ 59
def prefixEnd_6969967 : Nat := 4983230072969 + 3 ^ 40 * 6969967 * 2
def baseEnd_6969967 : Nat := 397660357441804078417579

theorem tailTrace_6969967 : CollatzResearch.WordTrace tailWord_6969967 prefixEnd_6969967 397660357441804078417579 := by
  unfold tailWord_6969967
  simp only [CollatzResearch.WordTrace]
  refine ⟨254215581140007409438068155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169477054093338272958712103 254215581140007409438068155)
  ·
    refine ⟨381323371710011114157102233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254215581140007409438068155 381323371710011114157102233)
    ·
      refine ⟨285992528782508335617826675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381323371710011114157102233 285992528782508335617826675)
      ·
        refine ⟨428988793173762503426740013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285992528782508335617826675 428988793173762503426740013)
        ·
          refine ⟨160870797440160938785027505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 428988793173762503426740013 160870797440160938785027505)
          ·
            refine ⟨120653098080120704088770629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160870797440160938785027505 120653098080120704088770629)
            ·
              refine ⟨22622455890022632016644493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120653098080120704088770629 22622455890022632016644493)
              ·
                refine ⟨8483420958758487006241685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22622455890022632016644493 8483420958758487006241685)
                ·
                  refine ⟨397660357441804078417579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8483420958758487006241685 397660357441804078417579)
                  ·
                    rfl

theorem cell23_6969967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 6].length) (baseStart_6969967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969967 prefixEnd_6969967 := by exact prefixLift 6969967
  have htrace : WordTrace (prefixWord ++ tailWord_6969967) baseStart_6969967 baseEnd_6969967 := by
    simpa [prefixWord, tailWord_6969967, baseEnd_6969967] using wordTrace_append hprefix tailTrace_6969967
  have hstable : (prefixWord ++ tailWord_6969967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969967).length < 2 ^ (prefixWord ++ tailWord_6969967).sum := by decide
  have hdescent : baseEnd_6969967 < baseStart_6969967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6969988 : List Nat := [2, 3, 2, 1, 3, 2, 2, 3, 1, 4]
def baseStart_6969988 : Nat := 118140960795 + 6969988 * 2 ^ 59
def prefixEnd_6969988 : Nat := 4983230072969 + 3 ^ 40 * 6969988 * 2
def baseEnd_6969988 : Nat := 1192984666689993707865205

theorem tailTrace_6969988 : CollatzResearch.WordTrace tailWord_6969988 prefixEnd_6969988 1192984666689993707865205 := by
  unfold tailWord_6969988
  simp only [CollatzResearch.WordTrace]
  refine ⟨127108173536465665012291309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169477564715287553349721745 127108173536465665012291309)
  ·
    refine ⟨47665565076174624379609241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127108173536465665012291309 47665565076174624379609241)
    ·
      refine ⟨35749173807130968284706931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47665565076174624379609241 35749173807130968284706931)
      ·
        refine ⟨53623760710696452427060397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35749173807130968284706931 53623760710696452427060397)
        ·
          refine ⟨20108910266511169660147649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53623760710696452427060397 20108910266511169660147649)
          ·
            refine ⟨15081682699883377245110737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20108910266511169660147649 15081682699883377245110737)
            ·
              refine ⟨11311262024912532933833053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15081682699883377245110737 11311262024912532933833053)
              ·
                refine ⟨4241723259342199850187395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11311262024912532933833053 4241723259342199850187395)
                ·
                  refine ⟨6362584889013299775281093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4241723259342199850187395 6362584889013299775281093)
                  ·
                    refine ⟨1192984666689993707865205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6362584889013299775281093 1192984666689993707865205)
                    ·
                      rfl

theorem cell23_6969988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_6969988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6969988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6969988 prefixEnd_6969988 := by exact prefixLift 6969988
  have htrace : WordTrace (prefixWord ++ tailWord_6969988) baseStart_6969988 baseEnd_6969988 := by
    simpa [prefixWord, tailWord_6969988, baseEnd_6969988] using wordTrace_append hprefix tailTrace_6969988
  have hstable : (prefixWord ++ tailWord_6969988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6969988).length < 2 ^ (prefixWord ++ tailWord_6969988).sum := by decide
  have hdescent : baseEnd_6969988 < baseStart_6969988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6969988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970004 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_6970004 : Nat := 118140960795 + 6970004 * 2 ^ 59
def prefixEnd_6970004 : Nat := 4983230072969 + 3 ^ 40 * 6970004 * 2
def baseEnd_6970004 : Nat := 3578962215760453060995541

theorem tailTrace_6970004 : CollatzResearch.WordTrace tailWord_6970004 prefixEnd_6970004 3578962215760453060995541 := by
  unfold tailWord_6970004
  simp only [CollatzResearch.WordTrace]
  refine ⟨127108465320436682378582533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169477953760582243171443377 127108465320436682378582533)
  ·
    refine ⟨23832837247581877945984225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127108465320436682378582533 23832837247581877945984225)
    ·
      refine ⟨17874627935686408459488169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23832837247581877945984225 17874627935686408459488169)
      ·
        refine ⟨13405970951764806344616127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17874627935686408459488169 13405970951764806344616127)
        ·
          refine ⟨20108956427647209516924191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13405970951764806344616127 20108956427647209516924191)
          ·
            refine ⟨30163434641470814275386287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20108956427647209516924191 30163434641470814275386287)
            ·
              refine ⟨45245151962206221413079431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30163434641470814275386287 45245151962206221413079431)
              ·
                refine ⟨67867727943309332119619147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45245151962206221413079431 67867727943309332119619147)
                ·
                  refine ⟨101801591914963998179428721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67867727943309332119619147 101801591914963998179428721)
                  ·
                    refine ⟨76351193936222998634571541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101801591914963998179428721 76351193936222998634571541)
                    ·
                      refine ⟨3578962215760453060995541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76351193936222998634571541 3578962215760453060995541)
                      ·
                        rfl

theorem cell23_6970004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_6970004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970004 prefixEnd_6970004 := by exact prefixLift 6970004
  have htrace : WordTrace (prefixWord ++ tailWord_6970004) baseStart_6970004 baseEnd_6970004 := by
    simpa [prefixWord, tailWord_6970004, baseEnd_6970004] using wordTrace_append hprefix tailTrace_6970004
  have hstable : (prefixWord ++ tailWord_6970004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970004).length < 2 ^ (prefixWord ++ tailWord_6970004).sum := by decide
  have hdescent : baseEnd_6970004 < baseStart_6970004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970034 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2]
def baseStart_6970034 : Nat := 118140960795 + 6970034 * 2 ^ 59
def prefixEnd_6970034 : Nat := 4983230072969 + 3 ^ 40 * 6970034 * 2
def baseEnd_6970034 : Nat := 3578977620180087943620403

theorem tailTrace_6970034 : CollatzResearch.WordTrace tailWord_6970034 prefixEnd_6970034 3578977620180087943620403 := by
  unfold tailWord_6970034
  simp only [CollatzResearch.WordTrace]
  refine ⟨63554506207691169970189289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169478683220509786587171437 63554506207691169970189289)
  ·
    refine ⟨47665879655768377477641967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63554506207691169970189289 47665879655768377477641967)
    ·
      refine ⟨71498819483652566216462951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47665879655768377477641967 71498819483652566216462951)
      ·
        refine ⟨107248229225478849324694427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71498819483652566216462951 107248229225478849324694427)
        ·
          refine ⟨160872343838218273987041641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107248229225478849324694427 160872343838218273987041641)
          ·
            refine ⟨120654257878663705490281231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160872343838218273987041641 120654257878663705490281231)
            ·
              refine ⟨180981386817995558235421847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120654257878663705490281231 180981386817995558235421847)
              ·
                refine ⟨271472080226993337353132771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180981386817995558235421847 271472080226993337353132771)
                ·
                  refine ⟨407208120340490006029699157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271472080226993337353132771 407208120340490006029699157)
                  ·
                    refine ⟨4771970160240117258160537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 407208120340490006029699157 4771970160240117258160537)
                    ·
                      refine ⟨3578977620180087943620403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4771970160240117258160537 3578977620180087943620403)
                      ·
                        rfl

theorem cell23_6970034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2].length) (baseStart_6970034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970034 prefixEnd_6970034 := by exact prefixLift 6970034
  have htrace : WordTrace (prefixWord ++ tailWord_6970034) baseStart_6970034 baseEnd_6970034 := by
    simpa [prefixWord, tailWord_6970034, baseEnd_6970034] using wordTrace_append hprefix tailTrace_6970034
  have hstable : (prefixWord ++ tailWord_6970034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970034).length < 2 ^ (prefixWord ++ tailWord_6970034).sum := by decide
  have hdescent : baseEnd_6970034 < baseStart_6970034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970044 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 6, 4]
def baseStart_6970044 : Nat := 118140960795 + 6970044 * 2 ^ 59
def prefixEnd_6970044 : Nat := 4983230072969 + 3 ^ 40 * 6970044 * 2
def baseEnd_6970044 : Nat := 1192994251662210968165119

theorem tailTrace_6970044 : CollatzResearch.WordTrace tailWord_6970044 prefixEnd_6970044 1192994251662210968165119 := by
  unfold tailWord_6970044
  simp only [CollatzResearch.WordTrace]
  refine ⟨127109194780364225794310593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169478926373818967725747457 127109194780364225794310593)
  ·
    refine ⟨95331896085273169345732945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127109194780364225794310593 95331896085273169345732945)
    ·
      refine ⟨71498922063954877009299709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95331896085273169345732945 71498922063954877009299709)
      ·
        refine ⟨26812095773983078878487391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71498922063954877009299709 26812095773983078878487391)
        ·
          refine ⟨40218143660974618317731087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26812095773983078878487391 40218143660974618317731087)
          ·
            refine ⟨60327215491461927476596631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40218143660974618317731087 60327215491461927476596631)
            ·
              refine ⟨90490823237192891214894947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60327215491461927476596631 90490823237192891214894947)
              ·
                refine ⟨135736234855789336822342421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90490823237192891214894947 135736234855789336822342421)
                ·
                  refine ⟨6362636008865125163547301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135736234855789336822342421 6362636008865125163547301)
                  ·
                    refine ⟨1192994251662210968165119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6362636008865125163547301 1192994251662210968165119)
                    ·
                      rfl

theorem cell23_6970044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_6970044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970044 prefixEnd_6970044 := by exact prefixLift 6970044
  have htrace : WordTrace (prefixWord ++ tailWord_6970044) baseStart_6970044 baseEnd_6970044 := by
    simpa [prefixWord, tailWord_6970044, baseEnd_6970044] using wordTrace_append hprefix tailTrace_6970044
  have hstable : (prefixWord ++ tailWord_6970044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970044).length < 2 ^ (prefixWord ++ tailWord_6970044).sum := by decide
  have hdescent : baseEnd_6970044 < baseStart_6970044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970045 : List Nat := [1, 4, 1, 2, 1, 5, 1, 3, 1, 1, 3]
def baseStart_6970045 : Nat := 118140960795 + 6970045 * 2 ^ 59
def prefixEnd_6970045 : Nat := 4983230072969 + 3 ^ 40 * 6970045 * 2
def baseEnd_6970045 : Nat := 3578983268467287400582853

theorem tailTrace_6970045 : CollatzResearch.WordTrace tailWord_6970045 prefixEnd_6970045 3578983268467287400582853 := by
  unfold tailWord_6970045
  simp only [CollatzResearch.WordTrace]
  refine ⟨254218426033724828759407589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169478950689149885839605059 254218426033724828759407589)
  ·
    refine ⟨47665954881323405392388923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254218426033724828759407589 47665954881323405392388923)
    ·
      refine ⟨71498932321985108088583385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47665954881323405392388923 71498932321985108088583385)
      ·
        refine ⟨53624199241488831066437539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71498932321985108088583385 53624199241488831066437539)
        ·
          refine ⟨80436298862233246599656309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53624199241488831066437539 80436298862233246599656309)
          ·
            refine ⟨7540903018334366868717779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80436298862233246599656309 7540903018334366868717779)
            ·
              refine ⟨11311354527501550303076669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7540903018334366868717779 11311354527501550303076669)
              ·
                refine ⟨4241757947813081363653751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11311354527501550303076669 4241757947813081363653751)
                ·
                  refine ⟨6362636921719622045480627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4241757947813081363653751 6362636921719622045480627)
                  ·
                    refine ⟨9543955382579433068220941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6362636921719622045480627 9543955382579433068220941)
                    ·
                      refine ⟨3578983268467287400582853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9543955382579433068220941 3578983268467287400582853)
                      ·
                        rfl

theorem cell23_6970045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_6970045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970045 prefixEnd_6970045 := by exact prefixLift 6970045
  have htrace : WordTrace (prefixWord ++ tailWord_6970045) baseStart_6970045 baseEnd_6970045 := by
    simpa [prefixWord, tailWord_6970045, baseEnd_6970045] using wordTrace_append hprefix tailTrace_6970045
  have hstable : (prefixWord ++ tailWord_6970045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970045).length < 2 ^ (prefixWord ++ tailWord_6970045).sum := by decide
  have hdescent : baseEnd_6970045 < baseStart_6970045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970117 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 3, 8]
def baseStart_6970117 : Nat := 118140960795 + 6970117 * 2 ^ 59
def prefixEnd_6970117 : Nat := 4983230072969 + 3 ^ 40 * 6970117 * 2
def baseEnd_6970117 : Nat := 1193006746358137039627507

theorem tailTrace_6970117 : CollatzResearch.WordTrace tailWord_6970117 prefixEnd_6970117 1193006746358137039627507 := by
  unfold tailWord_6970117
  simp only [CollatzResearch.WordTrace]
  refine ⟨254221052089463985056028605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169480701392975990037352403 254221052089463985056028605)
  ·
    refine ⟨95332894533548994396010727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254221052089463985056028605 95332894533548994396010727)
    ·
      refine ⟨142999341800323491594016091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95332894533548994396010727 142999341800323491594016091)
      ·
        refine ⟨214499012700485237391024137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142999341800323491594016091 214499012700485237391024137)
        ·
          refine ⟨160874259525363928043268103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214499012700485237391024137 160874259525363928043268103)
          ·
            refine ⟨241311389288045892064902155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160874259525363928043268103 241311389288045892064902155)
            ·
              refine ⟨361967083932068838097353233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241311389288045892064902155 361967083932068838097353233)
              ·
                refine ⟨271475312949051628573014925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361967083932068838097353233 271475312949051628573014925)
                ·
                  refine ⟨101803242355894360714880597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 271475312949051628573014925 101803242355894360714880597)
                  ·
                    refine ⟨1193006746358137039627507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101803242355894360714880597 1193006746358137039627507)
                    ·
                      rfl

theorem cell23_6970117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 8].length) (baseStart_6970117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970117 prefixEnd_6970117 := by exact prefixLift 6970117
  have htrace : WordTrace (prefixWord ++ tailWord_6970117) baseStart_6970117 baseEnd_6970117 := by
    simpa [prefixWord, tailWord_6970117, baseEnd_6970117] using wordTrace_append hprefix tailTrace_6970117
  have hstable : (prefixWord ++ tailWord_6970117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970117).length < 2 ^ (prefixWord ++ tailWord_6970117).sum := by decide
  have hdescent : baseEnd_6970117 < baseStart_6970117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970119 : List Nat := [1, 1, 4, 4, 1, 3, 2, 2, 1, 2, 2]
def baseStart_6970119 : Nat := 118140960795 + 6970119 * 2 ^ 59
def prefixEnd_6970119 : Nat := 4983230072969 + 3 ^ 40 * 6970119 * 2
def baseEnd_6970119 : Nat := 3579021266035720111057513

theorem tailTrace_6970119 : CollatzResearch.WordTrace tailWord_6970119 prefixEnd_6970119 3579021266035720111057513 := by
  unfold tailWord_6970119
  simp only [CollatzResearch.WordTrace]
  refine ⟨254221125035456739397601411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169480750023637826265067607 254221125035456739397601411)
  ·
    refine ⟨381331687553185109096402117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254221125035456739397601411 381331687553185109096402117)
    ·
      refine ⟨71499691416222207955575397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 381331687553185109096402117 71499691416222207955575397)
      ·
        refine ⟨13406192140541663991670387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71499691416222207955575397 13406192140541663991670387)
        ·
          refine ⟨20109288210812495987505581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13406192140541663991670387 20109288210812495987505581)
          ·
            refine ⟨7540983079054685995314593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20109288210812495987505581 7540983079054685995314593)
            ·
              refine ⟨5655737309291014496485945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7540983079054685995314593 5655737309291014496485945)
              ·
                refine ⟨4241802981968260872364459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5655737309291014496485945 4241802981968260872364459)
                ·
                  refine ⟨6362704472952391308546689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4241802981968260872364459 6362704472952391308546689)
                  ·
                    refine ⟨4772028354714293481410017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6362704472952391308546689 4772028354714293481410017)
                    ·
                      refine ⟨3579021266035720111057513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4772028354714293481410017 3579021266035720111057513)
                      ·
                        rfl

theorem cell23_6970119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_6970119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970119 prefixEnd_6970119 := by exact prefixLift 6970119
  have htrace : WordTrace (prefixWord ++ tailWord_6970119) baseStart_6970119 baseEnd_6970119 := by
    simpa [prefixWord, tailWord_6970119, baseEnd_6970119] using wordTrace_append hprefix tailTrace_6970119
  have hstable : (prefixWord ++ tailWord_6970119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970119).length < 2 ^ (prefixWord ++ tailWord_6970119).sum := by decide
  have hdescent : baseEnd_6970119 < baseStart_6970119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970175 : List Nat := [1, 1, 2, 2, 5, 1, 3, 2, 2, 2, 2]
def baseStart_6970175 : Nat := 118140960795 + 6970175 * 2 ^ 59
def prefixEnd_6970175 : Nat := 4983230072969 + 3 ^ 40 * 6970175 * 2
def baseEnd_6970175 : Nat := 3579050020952371891957255

theorem tailTrace_6970175 : CollatzResearch.WordTrace tailWord_6970175 prefixEnd_6970175 3579050020952371891957255 := by
  unfold tailWord_6970175
  simp only [CollatzResearch.WordTrace]
  refine ⟨254223167523253860961639979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169482111682169240641093319 254223167523253860961639979)
  ·
    refine ⟨381334751284880791442459969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254223167523253860961639979 381334751284880791442459969)
    ·
      refine ⟨286001063463660593581844977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381334751284880791442459969 286001063463660593581844977)
      ·
        refine ⟨214500797597745445186383733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286001063463660593581844977 214500797597745445186383733)
        ·
          refine ⟨20109449774788635486223475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 214500797597745445186383733 20109449774788635486223475)
          ·
            refine ⟨30164174662182953229335213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20109449774788635486223475 30164174662182953229335213)
            ·
              refine ⟨11311565498318607461000705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30164174662182953229335213 11311565498318607461000705)
              ·
                refine ⟨8483674123738955595750529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11311565498318607461000705 8483674123738955595750529)
                ·
                  refine ⟨6362755592804216696812897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8483674123738955595750529 6362755592804216696812897)
                  ·
                    refine ⟨4772066694603162522609673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6362755592804216696812897 4772066694603162522609673)
                    ·
                      refine ⟨3579050020952371891957255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4772066694603162522609673 3579050020952371891957255)
                      ·
                        rfl

theorem cell23_6970175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 2, 2, 2].length) (baseStart_6970175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970175 prefixEnd_6970175 := by exact prefixLift 6970175
  have htrace : WordTrace (prefixWord ++ tailWord_6970175) baseStart_6970175 baseEnd_6970175 := by
    simpa [prefixWord, tailWord_6970175, baseEnd_6970175] using wordTrace_append hprefix tailTrace_6970175
  have hstable : (prefixWord ++ tailWord_6970175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970175).length < 2 ^ (prefixWord ++ tailWord_6970175).sum := by decide
  have hdescent : baseEnd_6970175 < baseStart_6970175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970194 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 3, 7]
def baseStart_6970194 : Nat := 118140960795 + 6970194 * 2 ^ 59
def prefixEnd_6970194 : Nat := 4983230072969 + 3 ^ 40 * 6970194 * 2
def baseEnd_6970194 : Nat := 1193019925694935772539889

theorem tailTrace_6970194 : CollatzResearch.WordTrace tailWord_6970194 prefixEnd_6970194 1193019925694935772539889 := by
  unfold tailWord_6970194
  simp only [CollatzResearch.WordTrace]
  refine ⟨63555965127546256801645409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169482573673456684804387757 63555965127546256801645409)
  ·
    refine ⟨47666973845659692601234057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63555965127546256801645409 47666973845659692601234057)
    ·
      refine ⟨35750230384244769450925543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47666973845659692601234057 35750230384244769450925543)
      ·
        refine ⟨53625345576367154176388315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35750230384244769450925543 53625345576367154176388315)
        ·
          refine ⟨80438018364550731264582473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53625345576367154176388315 80438018364550731264582473)
          ·
            refine ⟨60328513773413048448436855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80438018364550731264582473 60328513773413048448436855)
            ·
              refine ⟨90492770660119572672655283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60328513773413048448436855 90492770660119572672655283)
              ·
                refine ⟨135739155990179359008982925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90492770660119572672655283 135739155990179359008982925)
                ·
                  refine ⟨50902183496317259628368597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135739155990179359008982925 50902183496317259628368597)
                  ·
                    refine ⟨1193019925694935772539889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50902183496317259628368597 1193019925694935772539889)
                    ·
                      rfl

theorem cell23_6970194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_6970194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970194 prefixEnd_6970194 := by exact prefixLift 6970194
  have htrace : WordTrace (prefixWord ++ tailWord_6970194) baseStart_6970194 baseEnd_6970194 := by
    simpa [prefixWord, tailWord_6970194, baseEnd_6970194] using wordTrace_append hprefix tailTrace_6970194
  have hstable : (prefixWord ++ tailWord_6970194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970194).length < 2 ^ (prefixWord ++ tailWord_6970194).sum := by decide
  have hdescent : baseEnd_6970194 < baseStart_6970194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970231 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 4, 4, 2]
def baseStart_6970231 : Nat := 118140960795 + 6970231 * 2 ^ 59
def prefixEnd_6970231 : Nat := 4983230072969 + 3 ^ 40 * 6970231 * 2
def baseEnd_6970231 : Nat := 3579078775869023672856997

theorem tailTrace_6970231 : CollatzResearch.WordTrace tailWord_6970231 prefixEnd_6970231 3579078775869023672856997 := by
  unfold tailWord_6970231
  simp only [CollatzResearch.WordTrace]
  refine ⟨254225210011050982525678547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169483473340700655017119031 254225210011050982525678547)
  ·
    refine ⟨381337815016576473788517821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254225210011050982525678547 381337815016576473788517821)
    ·
      refine ⟨143001680631216177670694183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 381337815016576473788517821 143001680631216177670694183)
      ·
        refine ⟨214502520946824266506041275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143001680631216177670694183 214502520946824266506041275)
        ·
          refine ⟨321753781420236399759061913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214502520946824266506041275 321753781420236399759061913)
          ·
            refine ⟨241315336065177299819296435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321753781420236399759061913 241315336065177299819296435)
            ·
              refine ⟨361973004097765949728944653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241315336065177299819296435 361973004097765949728944653)
              ·
                refine ⟨135739876536662231148354245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 361973004097765949728944653 135739876536662231148354245)
                ·
                  refine ⟨25451226850624168340316421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135739876536662231148354245 25451226850624168340316421)
                  ·
                    refine ⟨4772105034492031563809329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25451226850624168340316421 4772105034492031563809329)
                    ·
                      refine ⟨3579078775869023672856997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4772105034492031563809329 3579078775869023672856997)
                      ·
                        rfl

theorem cell23_6970231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 4, 2].length) (baseStart_6970231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970231 prefixEnd_6970231 := by exact prefixLift 6970231
  have htrace : WordTrace (prefixWord ++ tailWord_6970231) baseStart_6970231 baseEnd_6970231 := by
    simpa [prefixWord, tailWord_6970231, baseEnd_6970231] using wordTrace_append hprefix tailTrace_6970231
  have hstable : (prefixWord ++ tailWord_6970231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970231).length < 2 ^ (prefixWord ++ tailWord_6970231).sum := by decide
  have hdescent : baseEnd_6970231 < baseStart_6970231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970262 : List Nat := [5, 3, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_6970262 : Nat := 118140960795 + 6970262 * 2 ^ 59
def prefixEnd_6970262 : Nat := 4983230072969 + 3 ^ 40 * 6970262 * 2
def baseEnd_6970262 : Nat := 1193031564589771017189785

theorem tailTrace_6970262 : CollatzResearch.WordTrace tailWord_6970262 prefixEnd_6970262 1193031564589771017189785 := by
  unfold tailWord_6970262
  simp only [CollatzResearch.WordTrace]
  refine ⟨15889146292121167176253565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169484227115959116546704693 15889146292121167176253565)
  ·
    refine ⟨5958429859545437691095087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15889146292121167176253565 5958429859545437691095087)
    ·
      refine ⟨8937644789318156536642631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5958429859545437691095087 8937644789318156536642631)
      ·
        refine ⟨13406467183977234804963947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8937644789318156536642631 13406467183977234804963947)
        ·
          refine ⟨20109700775965852207445921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13406467183977234804963947 20109700775965852207445921)
          ·
            refine ⟨15082275581974389155584441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20109700775965852207445921 15082275581974389155584441)
            ·
              refine ⟨11311706686480791866688331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15082275581974389155584441 11311706686480791866688331)
              ·
                refine ⟨16967560029721187800032497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11311706686480791866688331 16967560029721187800032497)
                ·
                  refine ⟨12725670022290890850024373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16967560029721187800032497 12725670022290890850024373)
                  ·
                    refine ⟨1193031564589771017189785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12725670022290890850024373 1193031564589771017189785)
                    ·
                      rfl

theorem cell23_6970262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_6970262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970262 prefixEnd_6970262 := by exact prefixLift 6970262
  have htrace : WordTrace (prefixWord ++ tailWord_6970262) baseStart_6970262 baseEnd_6970262 := by
    simpa [prefixWord, tailWord_6970262, baseEnd_6970262] using wordTrace_append hprefix tailTrace_6970262
  have hstable : (prefixWord ++ tailWord_6970262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970262).length < 2 ^ (prefixWord ++ tailWord_6970262).sum := by decide
  have hdescent : baseEnd_6970262 < baseStart_6970262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970298 : List Nat := [3, 1, 1, 1, 2, 1, 4, 3, 3, 1, 3]
def baseStart_6970298 : Nat := 118140960795 + 6970298 * 2 ^ 59
def prefixEnd_6970298 : Nat := 4983230072969 + 3 ^ 40 * 6970298 * 2
def baseEnd_6970298 : Nat := 3579113179072874910719189

theorem tailTrace_6970298 : CollatzResearch.WordTrace tailWord_6970298 prefixEnd_6970298 3579113179072874910719189 := by
  unfold tailWord_6970298
  simp only [CollatzResearch.WordTrace]
  refine ⟨63556913425452063242091887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169485102467872168645578365 63556913425452063242091887)
  ·
    refine ⟨95335370138178094863137831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63556913425452063242091887 95335370138178094863137831)
    ·
      refine ⟨143003055207267142294706747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95335370138178094863137831 143003055207267142294706747)
      ·
        refine ⟨214504582810900713442060121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143003055207267142294706747 214504582810900713442060121)
        ·
          refine ⟨160878437108175535081545091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214504582810900713442060121 160878437108175535081545091)
          ·
            refine ⟨241317655662263302622317637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160878437108175535081545091 241317655662263302622317637)
            ·
              refine ⟨45247060436674369241684557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 241317655662263302622317637 45247060436674369241684557)
              ·
                refine ⟨16967647663752888465631709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45247060436674369241684557 16967647663752888465631709)
                ·
                  refine ⟨6362867873907333174611891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16967647663752888465631709 6362867873907333174611891)
                  ·
                    refine ⟨9544301810860999761917837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6362867873907333174611891 9544301810860999761917837)
                    ·
                      refine ⟨3579113179072874910719189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9544301810860999761917837 3579113179072874910719189)
                      ·
                        rfl

theorem cell23_6970298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 3, 1, 3].length) (baseStart_6970298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970298 prefixEnd_6970298 := by exact prefixLift 6970298
  have htrace : WordTrace (prefixWord ++ tailWord_6970298) baseStart_6970298 baseEnd_6970298 := by
    simpa [prefixWord, tailWord_6970298, baseEnd_6970298] using wordTrace_append hprefix tailTrace_6970298
  have hstable : (prefixWord ++ tailWord_6970298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970298).length < 2 ^ (prefixWord ++ tailWord_6970298).sum := by decide
  have hdescent : baseEnd_6970298 < baseStart_6970298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970321 : List Nat := [1, 2, 2, 1, 2, 1, 3, 3, 3, 1, 4]
def baseStart_6970321 : Nat := 118140960795 + 6970321 * 2 ^ 59
def prefixEnd_6970321 : Nat := 4983230072969 + 3 ^ 40 * 6970321 * 2
def baseEnd_6970321 : Nat := 3579124989127928320731583

theorem tailTrace_6970321 : CollatzResearch.WordTrace tailWord_6970321 prefixEnd_6970321 3579124989127928320731583 := by
  unfold tailWord_6970321
  simp only [CollatzResearch.WordTrace]
  refine ⟨254228492580724927896454817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169485661720483285264303211 254228492580724927896454817)
  ·
    refine ⟨190671369435543695922341113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254228492580724927896454817 190671369435543695922341113)
    ·
      refine ⟨143003527076657771941755835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190671369435543695922341113 143003527076657771941755835)
      ·
        refine ⟨214505290614986657912633753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143003527076657771941755835 214505290614986657912633753)
        ·
          refine ⟨160878967961239993434475315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214505290614986657912633753 160878967961239993434475315)
          ·
            refine ⟨241318451941859990151712973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160878967961239993434475315 241318451941859990151712973)
            ·
              refine ⟨90494419478197496306892365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241318451941859990151712973 90494419478197496306892365)
              ·
                refine ⟨33935407304324061115084637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90494419478197496306892365 33935407304324061115084637)
                ·
                  refine ⟨12725777739121522918156739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33935407304324061115084637 12725777739121522918156739)
                  ·
                    refine ⟨19088666608682284377235109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12725777739121522918156739 19088666608682284377235109)
                    ·
                      refine ⟨3579124989127928320731583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19088666608682284377235109 3579124989127928320731583)
                      ·
                        rfl

theorem cell23_6970321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_6970321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970321 prefixEnd_6970321 := by exact prefixLift 6970321
  have htrace : WordTrace (prefixWord ++ tailWord_6970321) baseStart_6970321 baseEnd_6970321 := by
    simpa [prefixWord, tailWord_6970321, baseEnd_6970321] using wordTrace_append hprefix tailTrace_6970321
  have hstable : (prefixWord ++ tailWord_6970321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970321).length < 2 ^ (prefixWord ++ tailWord_6970321).sum := by decide
  have hdescent : baseEnd_6970321 < baseStart_6970321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970325 : List Nat := [1, 3, 2, 3, 3, 1, 1, 1, 1, 5, 2]
def baseStart_6970325 : Nat := 118140960795 + 6970325 * 2 ^ 59
def prefixEnd_6970325 : Nat := 4983230072969 + 3 ^ 40 * 6970325 * 2
def baseEnd_6970325 : Nat := 3579127043050546305081565

theorem tailTrace_6970325 : CollatzResearch.WordTrace tailWord_6970325 prefixEnd_6970325 3579127043050546305081565 := by
  unfold tailWord_6970325
  simp only [CollatzResearch.WordTrace]
  refine ⟨254228638472710436579600429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169485758981806957719733619 254228638472710436579600429)
  ·
    refine ⟨95335739427266413717350161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254228638472710436579600429 95335739427266413717350161)
    ·
      refine ⟨71501804570449810288012621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95335739427266413717350161 71501804570449810288012621)
      ·
        refine ⟨26813176713918678858004733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71501804570449810288012621 26813176713918678858004733)
        ·
          refine ⟨10054941267719504571751775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26813176713918678858004733 10054941267719504571751775)
          ·
            refine ⟨15082411901579256857627663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10054941267719504571751775 15082411901579256857627663)
            ·
              refine ⟨22623617852368885286441495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15082411901579256857627663 22623617852368885286441495)
              ·
                refine ⟨33935426778553327929662243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22623617852368885286441495 33935426778553327929662243)
                ·
                  refine ⟨50903140167829991894493365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33935426778553327929662243 50903140167829991894493365)
                  ·
                    refine ⟨4772169390734061740108753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50903140167829991894493365 4772169390734061740108753)
                    ·
                      refine ⟨3579127043050546305081565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4772169390734061740108753 3579127043050546305081565)
                      ·
                        rfl

theorem cell23_6970325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_6970325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970325 prefixEnd_6970325 := by exact prefixLift 6970325
  have htrace : WordTrace (prefixWord ++ tailWord_6970325) baseStart_6970325 baseEnd_6970325 := by
    simpa [prefixWord, tailWord_6970325, baseEnd_6970325] using wordTrace_append hprefix tailTrace_6970325
  have hstable : (prefixWord ++ tailWord_6970325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970325).length < 2 ^ (prefixWord ++ tailWord_6970325).sum := by decide
  have hdescent : baseEnd_6970325 < baseStart_6970325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970356 : List Nat := [2, 6, 2, 1, 1, 1, 3, 1, 6]
def baseStart_6970356 : Nat := 118140960795 + 6970356 * 2 ^ 59
def prefixEnd_6970356 : Nat := 4983230072969 + 3 ^ 40 * 6970356 * 2
def baseEnd_6970356 : Nat := 397682551216759520421547

theorem tailTrace_6970356 : CollatzResearch.WordTrace tailWord_6970356 prefixEnd_6970356 397682551216759520421547 := by
  unfold tailWord_6970356
  simp only [CollatzResearch.WordTrace]
  refine ⟨127114884567799064436989461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169486512757065419249319281 127114884567799064436989461)
  ·
    refine ⟨5958510214115581145483881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 127114884567799064436989461 5958510214115581145483881)
    ·
      refine ⟨4468882660586685859112911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5958510214115581145483881 4468882660586685859112911)
      ·
        refine ⟨6703323990880028788669367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4468882660586685859112911 6703323990880028788669367)
        ·
          refine ⟨10054985986320043183004051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6703323990880028788669367 10054985986320043183004051)
          ·
            refine ⟨15082478979480064774506077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10054985986320043183004051 15082478979480064774506077)
            ·
              refine ⟨5655929617305024290439779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15082478979480064774506077 5655929617305024290439779)
              ·
                refine ⟨8483894425957536435659669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5655929617305024290439779 8483894425957536435659669)
                ·
                  refine ⟨397682551216759520421547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8483894425957536435659669 397682551216759520421547)
                  ·
                    rfl

theorem cell23_6970356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_6970356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970356 prefixEnd_6970356 := by exact prefixLift 6970356
  have htrace : WordTrace (prefixWord ++ tailWord_6970356) baseStart_6970356 baseEnd_6970356 := by
    simpa [prefixWord, tailWord_6970356, baseEnd_6970356] using wordTrace_append hprefix tailTrace_6970356
  have hstable : (prefixWord ++ tailWord_6970356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970356).length < 2 ^ (prefixWord ++ tailWord_6970356).sum := by decide
  have hdescent : baseEnd_6970356 < baseStart_6970356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970358 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5]
def baseStart_6970358 : Nat := 118140960795 + 6970358 * 2 ^ 59
def prefixEnd_6970358 : Nat := 4983230072969 + 3 ^ 40 * 6970358 * 2
def baseEnd_6970358 : Nat := 3579143987912144675968913

theorem tailTrace_6970358 : CollatzResearch.WordTrace tailWord_6970358 prefixEnd_6970358 3579143987912144675968913 := by
  unfold tailWord_6970358
  simp only [CollatzResearch.WordTrace]
  refine ⟨15889365130099430200971983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169486561387727255477034485 15889365130099430200971983)
  ·
    refine ⟨23834047695149145301457975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15889365130099430200971983 23834047695149145301457975)
    ·
      refine ⟨35751071542723717952186963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23834047695149145301457975 35751071542723717952186963)
      ·
        refine ⟨53626607314085576928280445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35751071542723717952186963 53626607314085576928280445)
        ·
          refine ⟨20109977742782091348105167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53626607314085576928280445 20109977742782091348105167)
          ·
            refine ⟨30164966614173137022157751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20109977742782091348105167 30164966614173137022157751)
            ·
              refine ⟨45247449921259705533236627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30164966614173137022157751 45247449921259705533236627)
              ·
                refine ⟨67871174881889558299854941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45247449921259705533236627 67871174881889558299854941)
                ·
                  refine ⟨25451690580708584362445603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67871174881889558299854941 25451690580708584362445603)
                  ·
                    refine ⟨38177535871062876543668405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25451690580708584362445603 38177535871062876543668405)
                    ·
                      refine ⟨3579143987912144675968913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38177535871062876543668405 3579143987912144675968913)
                      ·
                        rfl

theorem cell23_6970358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_6970358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970358 prefixEnd_6970358 := by exact prefixLift 6970358
  have htrace : WordTrace (prefixWord ++ tailWord_6970358) baseStart_6970358 baseEnd_6970358 := by
    simpa [prefixWord, tailWord_6970358, baseEnd_6970358] using wordTrace_append hprefix tailTrace_6970358
  have hstable : (prefixWord ++ tailWord_6970358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970358).length < 2 ^ (prefixWord ++ tailWord_6970358).sum := by decide
  have hdescent : baseEnd_6970358 < baseStart_6970358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970375 : List Nat := [1, 1, 4, 3, 1, 1, 4, 2, 1, 2, 3]
def baseStart_6970375 : Nat := 118140960795 + 6970375 * 2 ^ 59
def prefixEnd_6970375 : Nat := 4983230072969 + 3 ^ 40 * 6970375 * 2
def baseEnd_6970375 : Nat := 3579152717083271109456335

theorem tailTrace_6970375 : CollatzResearch.WordTrace tailWord_6970375 prefixEnd_6970375 3579152717083271109456335 := by
  unfold tailWord_6970375
  simp only [CollatzResearch.WordTrace]
  refine ⟨254230462122529295118920579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169486974748352863412613719 254230462122529295118920579)
  ·
    refine ⟨381345693183793942678380869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254230462122529295118920579 381345693183793942678380869)
    ·
      refine ⟨71502317471961364252196413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 381345693183793942678380869 71502317471961364252196413)
      ·
        refine ⟨26813369051985511594573655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71502317471961364252196413 26813369051985511594573655)
        ·
          refine ⟨40220053577978267391860483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26813369051985511594573655 40220053577978267391860483)
          ·
            refine ⟨60330080366967401087790725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40220053577978267391860483 60330080366967401087790725)
            ·
              refine ⟨11311890068806387703960761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60330080366967401087790725 11311890068806387703960761)
              ·
                refine ⟨8483917551604790777970571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11311890068806387703960761 8483917551604790777970571)
                ·
                  refine ⟨12725876327407186166955857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8483917551604790777970571 12725876327407186166955857)
                  ·
                    refine ⟨9544407245555389625216893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12725876327407186166955857 9544407245555389625216893)
                    ·
                      refine ⟨3579152717083271109456335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9544407245555389625216893 3579152717083271109456335)
                      ·
                        rfl

theorem cell23_6970375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_6970375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970375 prefixEnd_6970375 := by exact prefixLift 6970375
  have htrace : WordTrace (prefixWord ++ tailWord_6970375) baseStart_6970375 baseEnd_6970375 := by
    simpa [prefixWord, tailWord_6970375, baseEnd_6970375] using wordTrace_append hprefix tailTrace_6970375
  have hstable : (prefixWord ++ tailWord_6970375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970375).length < 2 ^ (prefixWord ++ tailWord_6970375).sum := by decide
  have hdescent : baseEnd_6970375 < baseStart_6970375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970378 : List Nat := [3, 1, 2, 2, 3, 1, 4, 7]
def baseStart_6970378 : Nat := 118140960795 + 6970378 * 2 ^ 59
def prefixEnd_6970378 : Nat := 4983230072969 + 3 ^ 40 * 6970378 * 2
def baseEnd_6970378 : Nat := 132561268797230911026623

theorem tailTrace_6970378 : CollatzResearch.WordTrace tailWord_6970378 prefixEnd_6970378 132561268797230911026623 := by
  unfold tailWord_6970378
  simp only [CollatzResearch.WordTrace]
  refine ⟨63557642885379606657819947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169487047694345617754186525 63557642885379606657819947)
  ·
    refine ⟨95336464328069409986729921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63557642885379606657819947 95336464328069409986729921)
    ·
      refine ⟨71502348246052057490047441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95336464328069409986729921 71502348246052057490047441)
      ·
        refine ⟨53626761184539043117535581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71502348246052057490047441 53626761184539043117535581)
        ·
          refine ⟨20110035444202141169075843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53626761184539043117535581 20110035444202141169075843)
          ·
            refine ⟨30165053166303211753613765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20110035444202141169075843 30165053166303211753613765)
            ·
              refine ⟨5655947468681852203802581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30165053166303211753613765 5655947468681852203802581)
              ·
                refine ⟨132561268797230911026623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5655947468681852203802581 132561268797230911026623)
                ·
                  rfl

theorem cell23_6970378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 7].length) (baseStart_6970378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970378 prefixEnd_6970378 := by exact prefixLift 6970378
  have htrace : WordTrace (prefixWord ++ tailWord_6970378) baseStart_6970378 baseEnd_6970378 := by
    simpa [prefixWord, tailWord_6970378, baseEnd_6970378] using wordTrace_append hprefix tailTrace_6970378
  have hstable : (prefixWord ++ tailWord_6970378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970378).length < 2 ^ (prefixWord ++ tailWord_6970378).sum := by decide
  have hdescent : baseEnd_6970378 < baseStart_6970378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970389 : List Nat := [1, 3, 2, 1, 4, 1, 3, 3, 1, 2, 2]
def baseStart_6970389 : Nat := 118140960795 + 6970389 * 2 ^ 59
def prefixEnd_6970389 : Nat := 4983230072969 + 3 ^ 40 * 6970389 * 2
def baseEnd_6970389 : Nat := 3579159905812434054681271

theorem tailTrace_6970389 : CollatzResearch.WordTrace tailWord_6970389 prefixEnd_6970389 3579159905812434054681271 := by
  unfold tailWord_6970389
  simp only [CollatzResearch.WordTrace]
  refine ⟨254230972744478575509930221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169487315162985717006620147 254230972744478575509930221)
  ·
    refine ⟨95336614779179465816223833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254230972744478575509930221 95336614779179465816223833)
    ·
      refine ⟨71502461084384599362167875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95336614779179465816223833 71502461084384599362167875)
      ·
        refine ⟨107253691626576899043251813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71502461084384599362167875 107253691626576899043251813)
        ·
          refine ⟨20110067179983168570609715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107253691626576899043251813 20110067179983168570609715)
          ·
            refine ⟨30165100769974752855914573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20110067179983168570609715 30165100769974752855914573)
            ·
              refine ⟨11311912788740532320967965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30165100769974752855914573 11311912788740532320967965)
              ·
                refine ⟨4241967295777699620362987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11311912788740532320967965 4241967295777699620362987)
                ·
                  refine ⟨6362950943666549430544481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4241967295777699620362987 6362950943666549430544481)
                  ·
                    refine ⟨4772213207749912072908361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6362950943666549430544481 4772213207749912072908361)
                    ·
                      refine ⟨3579159905812434054681271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4772213207749912072908361 3579159905812434054681271)
                      ·
                        rfl

theorem cell23_6970389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 3, 1, 2, 2].length) (baseStart_6970389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970389 prefixEnd_6970389 := by exact prefixLift 6970389
  have htrace : WordTrace (prefixWord ++ tailWord_6970389) baseStart_6970389 baseEnd_6970389 := by
    simpa [prefixWord, tailWord_6970389, baseEnd_6970389] using wordTrace_append hprefix tailTrace_6970389
  have hstable : (prefixWord ++ tailWord_6970389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970389).length < 2 ^ (prefixWord ++ tailWord_6970389).sum := by decide
  have hdescent : baseEnd_6970389 < baseStart_6970389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970405 : List Nat := [1, 3, 1, 2, 2, 2, 2, 4, 2, 1, 3]
def baseStart_6970405 : Nat := 118140960795 + 6970405 * 2 ^ 59
def prefixEnd_6970405 : Nat := 4983230072969 + 3 ^ 40 * 6970405 * 2
def baseEnd_6970405 : Nat := 3579168121502905992081197

theorem tailTrace_6970405 : CollatzResearch.WordTrace tailWord_6970405 prefixEnd_6970405 3579168121502905992081197 := by
  unfold tailWord_6970405
  simp only [CollatzResearch.WordTrace]
  refine ⟨254231556312420610242512669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169487704208280406828341779 254231556312420610242512669)
  ·
    refine ⟨95336833617157728840942251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254231556312420610242512669 95336833617157728840942251)
    ·
      refine ⟨143005250425736593261413377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95336833617157728840942251 143005250425736593261413377)
      ·
        refine ⟨107253937819302444946060033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143005250425736593261413377 107253937819302444946060033)
        ·
          refine ⟨80440453364476833709545025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107253937819302444946060033 80440453364476833709545025)
          ·
            refine ⟨60330340023357625282158769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80440453364476833709545025 60330340023357625282158769)
            ·
              refine ⟨45247755017518218961619077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60330340023357625282158769 45247755017518218961619077)
              ·
                refine ⟨8483954065784666055303577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45247755017518218961619077 8483954065784666055303577)
                ·
                  refine ⟨6362965549338499541477683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8483954065784666055303577 6362965549338499541477683)
                  ·
                    refine ⟨9544448324007749312216525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6362965549338499541477683 9544448324007749312216525)
                    ·
                      refine ⟨3579168121502905992081197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9544448324007749312216525 3579168121502905992081197)
                      ·
                        rfl

theorem cell23_6970405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_6970405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970405 prefixEnd_6970405 := by exact prefixLift 6970405
  have htrace : WordTrace (prefixWord ++ tailWord_6970405) baseStart_6970405 baseEnd_6970405 := by
    simpa [prefixWord, tailWord_6970405, baseEnd_6970405] using wordTrace_append hprefix tailTrace_6970405
  have hstable : (prefixWord ++ tailWord_6970405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970405).length < 2 ^ (prefixWord ++ tailWord_6970405).sum := by decide
  have hdescent : baseEnd_6970405 < baseStart_6970405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970411 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 4]
def baseStart_6970411 : Nat := 118140960795 + 6970411 * 2 ^ 59
def prefixEnd_6970411 : Nat := 4983230072969 + 3 ^ 40 * 6970411 * 2
def baseEnd_6970411 : Nat := 3579171202386832968606169

theorem tailTrace_6970411 : CollatzResearch.WordTrace tailWord_6970411 prefixEnd_6970411 3579171202386832968606169 := by
  unfold tailWord_6970411
  simp only [CollatzResearch.WordTrace]
  refine ⟨254231775150398873267231087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169487850100265915511487391 254231775150398873267231087)
  ·
    refine ⟨381347662725598309900846631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254231775150398873267231087 381347662725598309900846631)
    ·
      refine ⟨572021494088397464851269947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381347662725598309900846631 572021494088397464851269947)
      ·
        refine ⟨858032241132596197276904921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572021494088397464851269947 858032241132596197276904921)
        ·
          refine ⟨643524180849447147957678691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 858032241132596197276904921 643524180849447147957678691)
          ·
            refine ⟨965286271274170721936518037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643524180849447147957678691 965286271274170721936518037)
            ·
              refine ⟨45247793965976752590774283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 965286271274170721936518037 45247793965976752590774283)
              ·
                refine ⟨67871690948965128886161425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45247793965976752590774283 67871690948965128886161425)
                ·
                  refine ⟨50903768211723846664621069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67871690948965128886161425 50903768211723846664621069)
                  ·
                    refine ⟨19088913079396442499232901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50903768211723846664621069 19088913079396442499232901)
                    ·
                      refine ⟨3579171202386832968606169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19088913079396442499232901 3579171202386832968606169)
                      ·
                        rfl

theorem cell23_6970411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 4].length) (baseStart_6970411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970411 prefixEnd_6970411 := by exact prefixLift 6970411
  have htrace : WordTrace (prefixWord ++ tailWord_6970411) baseStart_6970411 baseEnd_6970411 := by
    simpa [prefixWord, tailWord_6970411, baseEnd_6970411] using wordTrace_append hprefix tailTrace_6970411
  have hstable : (prefixWord ++ tailWord_6970411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970411).length < 2 ^ (prefixWord ++ tailWord_6970411).sum := by decide
  have hdescent : baseEnd_6970411 < baseStart_6970411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970421 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 1, 8]
def baseStart_6970421 : Nat := 118140960795 + 6970421 * 2 ^ 59
def prefixEnd_6970421 : Nat := 4983230072969 + 3 ^ 40 * 6970421 * 2
def baseEnd_6970421 : Nat := 1193058779064459309827041

theorem tailTrace_6970421 : CollatzResearch.WordTrace tailWord_6970421 prefixEnd_6970421 1193058779064459309827041 := by
  unfold tailWord_6970421
  simp only [CollatzResearch.WordTrace]
  refine ⟨254232139880362644975095117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169488093253575096650063411 254232139880362644975095117)
  ·
    refine ⟨95337052455135991865660669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254232139880362644975095117 95337052455135991865660669)
    ·
      refine ⟨35751394670675996949622751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95337052455135991865660669 35751394670675996949622751)
      ·
        refine ⟨53627092006013995424434127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35751394670675996949622751 53627092006013995424434127)
        ·
          refine ⟨80440638009020993136651191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53627092006013995424434127 80440638009020993136651191)
          ·
            refine ⟨120660957013531489704976787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80440638009020993136651191 120660957013531489704976787)
            ·
              refine ⟨180991435520297234557465181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120660957013531489704976787 180991435520297234557465181)
              ·
                refine ⟨67871788320111462959049443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180991435520297234557465181 67871788320111462959049443)
                ·
                  refine ⟨101807682480167194438574165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67871788320111462959049443 101807682480167194438574165)
                  ·
                    refine ⟨1193058779064459309827041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101807682480167194438574165 1193058779064459309827041)
                    ·
                      rfl

theorem cell23_6970421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_6970421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970421 prefixEnd_6970421 := by exact prefixLift 6970421
  have htrace : WordTrace (prefixWord ++ tailWord_6970421) baseStart_6970421 baseEnd_6970421 := by
    simpa [prefixWord, tailWord_6970421, baseEnd_6970421] using wordTrace_append hprefix tailTrace_6970421
  have hstable : (prefixWord ++ tailWord_6970421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970421).length < 2 ^ (prefixWord ++ tailWord_6970421).sum := by decide
  have hdescent : baseEnd_6970421 < baseStart_6970421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970441 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 3, 4, 4]
def baseStart_6970441 : Nat := 118140960795 + 6970441 * 2 ^ 59
def prefixEnd_6970441 : Nat := 4983230072969 + 3 ^ 40 * 6970441 * 2
def baseEnd_6970441 : Nat := 3579186606806467851231031

theorem tailTrace_6970441 : CollatzResearch.WordTrace tailWord_6970441 prefixEnd_6970441 3579186606806467851231031 := by
  unfold tailWord_6970441
  simp only [CollatzResearch.WordTrace]
  refine ⟨254232869340290188390823177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169488579560193458927215451 254232869340290188390823177)
  ·
    refine ⟨190674652005217641293117383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254232869340290188390823177 190674652005217641293117383)
    ·
      refine ⟨286011978007826461939676075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190674652005217641293117383 286011978007826461939676075)
      ·
        refine ⟨429017967011739692909514113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286011978007826461939676075 429017967011739692909514113)
        ·
          refine ⟨321763475258804769682135585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429017967011739692909514113 321763475258804769682135585)
          ·
            refine ⟨241322606444103577261601689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321763475258804769682135585 241322606444103577261601689)
            ·
              refine ⟨180991954833077682946201267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241322606444103577261601689 180991954833077682946201267)
              ·
                refine ⟨271487932249616524419301901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180991954833077682946201267 271487932249616524419301901)
                ·
                  refine ⟨101807974593606196657238213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 271487932249616524419301901 101807974593606196657238213)
                  ·
                    refine ⟨19088995236301161873232165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101807974593606196657238213 19088995236301161873232165)
                    ·
                      refine ⟨3579186606806467851231031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19088995236301161873232165 3579186606806467851231031)
                      ·
                        rfl

theorem cell23_6970441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 4, 4].length) (baseStart_6970441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970441 prefixEnd_6970441 := by exact prefixLift 6970441
  have htrace : WordTrace (prefixWord ++ tailWord_6970441) baseStart_6970441 baseEnd_6970441 := by
    simpa [prefixWord, tailWord_6970441, baseEnd_6970441] using wordTrace_append hprefix tailTrace_6970441
  have hstable : (prefixWord ++ tailWord_6970441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970441).length < 2 ^ (prefixWord ++ tailWord_6970441).sum := by decide
  have hdescent : baseEnd_6970441 < baseStart_6970441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970462 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_6970462 : Nat := 118140960795 + 6970462 * 2 ^ 59
def prefixEnd_6970462 : Nat := 4983230072969 + 3 ^ 40 * 6970462 * 2
def baseEnd_6970462 : Nat := 3579197389900212269068435

theorem tailTrace_6970462 : CollatzResearch.WordTrace tailWord_6970462 prefixEnd_6970462 3579197389900212269068435 := by
  unfold tailWord_6970462
  simp only [CollatzResearch.WordTrace]
  refine ⟨31779204409151763622167205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169489090182142739318225093 31779204409151763622167205)
  ·
    refine ⟨5958600826715955679156351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31779204409151763622167205 5958600826715955679156351)
    ·
      refine ⟨8937901240073933518734527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5958600826715955679156351 8937901240073933518734527)
      ·
        refine ⟨13406851860110900278101791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8937901240073933518734527 13406851860110900278101791)
        ·
          refine ⟨20110277790166350417152687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13406851860110900278101791 20110277790166350417152687)
          ·
            refine ⟨30165416685249525625729031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20110277790166350417152687 30165416685249525625729031)
            ·
              refine ⟨45248125027874288438593547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30165416685249525625729031 45248125027874288438593547)
              ·
                refine ⟨67872187541811432657890321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45248125027874288438593547 67872187541811432657890321)
                ·
                  refine ⟨50904140656358574493417741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67872187541811432657890321 50904140656358574493417741)
                  ·
                    refine ⟨19089052746134465435031653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50904140656358574493417741 19089052746134465435031653)
                    ·
                      refine ⟨3579197389900212269068435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19089052746134465435031653 3579197389900212269068435)
                      ·
                        rfl

theorem cell23_6970462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_6970462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970462 prefixEnd_6970462 := by exact prefixLift 6970462
  have htrace : WordTrace (prefixWord ++ tailWord_6970462) baseStart_6970462 baseEnd_6970462 := by
    simpa [prefixWord, tailWord_6970462, baseEnd_6970462] using wordTrace_append hprefix tailTrace_6970462
  have hstable : (prefixWord ++ tailWord_6970462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970462).length < 2 ^ (prefixWord ++ tailWord_6970462).sum := by decide
  have hdescent : baseEnd_6970462 < baseStart_6970462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970491 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 7]
def baseStart_6970491 : Nat := 118140960795 + 6970491 * 2 ^ 59
def prefixEnd_6970491 : Nat := 4983230072969 + 3 ^ 40 * 6970491 * 2
def baseEnd_6970491 : Nat := 3579212280839192655605801

theorem tailTrace_6970491 : CollatzResearch.WordTrace tailWord_6970491 prefixEnd_6970491 3579212280839192655605801 := by
  unfold tailWord_6970491
  simp only [CollatzResearch.WordTrace]
  refine ⟨254234692990109046930143327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169489795326739364620095551 254234692990109046930143327)
  ·
    refine ⟨381352039485163570395214991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254234692990109046930143327 381352039485163570395214991)
    ·
      refine ⟨572028059227745355592822487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381352039485163570395214991 572028059227745355592822487)
      ·
        refine ⟨858042088841618033389233731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572028059227745355592822487 858042088841618033389233731)
        ·
          refine ⟨1287063133262427050083850597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 858042088841618033389233731 1287063133262427050083850597)
          ·
            refine ⟨241324337486705071890721987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1287063133262427050083850597 241324337486705071890721987)
            ·
              refine ⟨361986506230057607836082981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241324337486705071890721987 361986506230057607836082981)
              ·
                refine ⟨67872469918135801469265559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 361986506230057607836082981 67872469918135801469265559)
                ·
                  refine ⟨101808704877203702203898339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67872469918135801469265559 101808704877203702203898339)
                  ·
                    refine ⟨152713057315805553305847509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101808704877203702203898339 152713057315805553305847509)
                    ·
                      refine ⟨3579212280839192655605801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152713057315805553305847509 3579212280839192655605801)
                      ·
                        rfl

theorem cell23_6970491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 7].length) (baseStart_6970491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970491 prefixEnd_6970491 := by exact prefixLift 6970491
  have htrace : WordTrace (prefixWord ++ tailWord_6970491) baseStart_6970491 baseEnd_6970491 := by
    simpa [prefixWord, tailWord_6970491, baseEnd_6970491] using wordTrace_append hprefix tailTrace_6970491
  have hstable : (prefixWord ++ tailWord_6970491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970491).length < 2 ^ (prefixWord ++ tailWord_6970491).sum := by decide
  have hdescent : baseEnd_6970491 < baseStart_6970491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970535 : List Nat := [1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_6970535 : Nat := 118140960795 + 6970535 * 2 ^ 59
def prefixEnd_6970535 : Nat := 4983230072969 + 3 ^ 40 * 6970535 * 2
def baseEnd_6970535 : Nat := 3579234873987990483455599

theorem tailTrace_6970535 : CollatzResearch.WordTrace tailWord_6970535 prefixEnd_6970535 3579234873987990483455599 := by
  unfold tailWord_6970535
  simp only [CollatzResearch.WordTrace]
  refine ⟨254236297801949642444745059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169490865201299761629830039 254236297801949642444745059)
  ·
    refine ⟨381354446702924463667117589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254236297801949642444745059 381354446702924463667117589)
    ·
      refine ⟨17875989689199584234396137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 381354446702924463667117589 17875989689199584234396137)
      ·
        refine ⟨13406992266899688175797103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17875989689199584234396137 13406992266899688175797103)
        ·
          refine ⟨20110488400349532263695655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13406992266899688175797103 20110488400349532263695655)
          ·
            refine ⟨30165732600524298395543483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20110488400349532263695655 30165732600524298395543483)
            ·
              refine ⟨45248598900786447593315225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30165732600524298395543483 45248598900786447593315225)
              ·
                refine ⟨33936449175589835694986419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45248598900786447593315225 33936449175589835694986419)
                ·
                  refine ⟨50904673763384753542479629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33936449175589835694986419 50904673763384753542479629)
                  ·
                    refine ⟨19089252661269282578429861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50904673763384753542479629 19089252661269282578429861)
                    ·
                      refine ⟨3579234873987990483455599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19089252661269282578429861 3579234873987990483455599)
                      ·
                        rfl

theorem cell23_6970535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_6970535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970535 prefixEnd_6970535 := by exact prefixLift 6970535
  have htrace : WordTrace (prefixWord ++ tailWord_6970535) baseStart_6970535 baseEnd_6970535 := by
    simpa [prefixWord, tailWord_6970535, baseEnd_6970535] using wordTrace_append hprefix tailTrace_6970535
  have hstable : (prefixWord ++ tailWord_6970535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970535).length < 2 ^ (prefixWord ++ tailWord_6970535).sum := by decide
  have hdescent : baseEnd_6970535 < baseStart_6970535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970566 : List Nat := [6, 1, 2, 2, 1, 1, 1, 2, 2, 5]
def baseStart_6970566 : Nat := 118140960795 + 6970566 * 2 ^ 59
def prefixEnd_6970566 : Nat := 4983230072969 + 3 ^ 40 * 6970566 * 2
def baseEnd_6970566 : Nat := 1193083597296093287389319

theorem tailTrace_6970566 : CollatzResearch.WordTrace tailWord_6970566 prefixEnd_6970566 1193083597296093287389319 := by
  unfold tailWord_6970566
  simp only [CollatzResearch.WordTrace]
  refine ⟨7944919639526166710597611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 169491618976558223159415701 7944919639526166710597611)
  ·
    refine ⟨11917379459289250065896417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7944919639526166710597611 11917379459289250065896417)
    ·
      refine ⟨8938034594466937549422313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11917379459289250065896417 8938034594466937549422313)
      ·
        refine ⟨6703525945850203162066735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8938034594466937549422313 6703525945850203162066735)
        ·
          refine ⟨10055288918775304743100103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6703525945850203162066735 10055288918775304743100103)
          ·
            refine ⟨15082933378162957114650155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10055288918775304743100103 15082933378162957114650155)
            ·
              refine ⟨22624400067244435671975233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15082933378162957114650155 22624400067244435671975233)
              ·
                refine ⟨16968300050433326753981425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22624400067244435671975233 16968300050433326753981425)
                ·
                  refine ⟨12726225037824995065486069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16968300050433326753981425 12726225037824995065486069)
                  ·
                    refine ⟨1193083597296093287389319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12726225037824995065486069 1193083597296093287389319)
                    ·
                      rfl

theorem cell23_6970566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_6970566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970566 prefixEnd_6970566 := by exact prefixLift 6970566
  have htrace : WordTrace (prefixWord ++ tailWord_6970566) baseStart_6970566 baseEnd_6970566 := by
    simpa [prefixWord, tailWord_6970566, baseEnd_6970566] using wordTrace_append hprefix tailTrace_6970566
  have hstable : (prefixWord ++ tailWord_6970566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970566).length < 2 ^ (prefixWord ++ tailWord_6970566).sum := by decide
  have hdescent : baseEnd_6970566 < baseStart_6970566 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970592 : List Nat := [2, 1, 1, 3, 1, 6, 2, 1, 6]
def baseStart_6970592 : Nat := 118140960795 + 6970592 * 2 ^ 59
def prefixEnd_6970592 : Nat := 4983230072969 + 3 ^ 40 * 6970592 * 2
def baseEnd_6970592 : Nat := 397696015820588528938093

theorem tailTrace_6970592 : CollatzResearch.WordTrace tailWord_6970592 prefixEnd_6970592 397696015820588528938093 := by
  unfold tailWord_6970592
  simp only [CollatzResearch.WordTrace]
  refine ⟨127119188381371570589785015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169492251175162094119713353 127119188381371570589785015)
  ·
    refine ⟨190678782572057355884677523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127119188381371570589785015 190678782572057355884677523)
    ·
      refine ⟨286018173858086033827016285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190678782572057355884677523 286018173858086033827016285)
      ·
        refine ⟨107256815196782262685131107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286018173858086033827016285 107256815196782262685131107)
        ·
          refine ⟨160885222795173394027696661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107256815196782262685131107 160885222795173394027696661)
          ·
            refine ⟨7541494818523752845048281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 160885222795173394027696661 7541494818523752845048281)
            ·
              refine ⟨5656121113892814633786211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7541494818523752845048281 5656121113892814633786211)
              ·
                refine ⟨8484181670839221950679317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5656121113892814633786211 8484181670839221950679317)
                ·
                  refine ⟨397696015820588528938093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8484181670839221950679317 397696015820588528938093)
                  ·
                    rfl

theorem cell23_6970592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 6].length) (baseStart_6970592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970592 prefixEnd_6970592 := by exact prefixLift 6970592
  have htrace : WordTrace (prefixWord ++ tailWord_6970592) baseStart_6970592 baseEnd_6970592 := by
    simpa [prefixWord, tailWord_6970592, baseEnd_6970592] using wordTrace_append hprefix tailTrace_6970592
  have hstable : (prefixWord ++ tailWord_6970592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970592).length < 2 ^ (prefixWord ++ tailWord_6970592).sum := by decide
  have hdescent : baseEnd_6970592 < baseStart_6970592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970636 : List Nat := [2, 2, 1, 2, 2, 3, 4, 2, 1, 1, 3]
def baseStart_6970636 : Nat := 118140960795 + 6970636 * 2 ^ 59
def prefixEnd_6970636 : Nat := 4983230072969 + 3 ^ 40 * 6970636 * 2
def baseEnd_6970636 : Nat := 3579286735534094588292635

theorem tailTrace_6970636 : CollatzResearch.WordTrace tailWord_6970636 prefixEnd_6970636 3579286735534094588292635 := by
  unfold tailWord_6970636
  simp only [CollatzResearch.WordTrace]
  refine ⟨127119990787291868347085881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169493321049722491129447841 127119990787291868347085881)
  ·
    refine ⟨95339993090468901260314411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127119990787291868347085881 95339993090468901260314411)
    ·
      refine ⟨143009989635703351890471617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95339993090468901260314411 143009989635703351890471617)
      ·
        refine ⟨107257492226777513917853713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143009989635703351890471617 107257492226777513917853713)
        ·
          refine ⟨80443119170083135438390285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107257492226777513917853713 80443119170083135438390285)
          ·
            refine ⟨30166169688781175789396357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80443119170083135438390285 30166169688781175789396357)
            ·
              refine ⟨5656156816646470460511817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30166169688781175789396357 5656156816646470460511817)
              ·
                refine ⟨4242117612484852845383863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5656156816646470460511817 4242117612484852845383863)
                ·
                  refine ⟨6363176418727279268075795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4242117612484852845383863 6363176418727279268075795)
                  ·
                    refine ⟨9544764628090918902113693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6363176418727279268075795 9544764628090918902113693)
                    ·
                      refine ⟨3579286735534094588292635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9544764628090918902113693 3579286735534094588292635)
                      ·
                        rfl

theorem cell23_6970636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 2, 1, 1, 3].length) (baseStart_6970636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970636 prefixEnd_6970636 := by exact prefixLift 6970636
  have htrace : WordTrace (prefixWord ++ tailWord_6970636) baseStart_6970636 baseEnd_6970636 := by
    simpa [prefixWord, tailWord_6970636, baseEnd_6970636] using wordTrace_append hprefix tailTrace_6970636
  have hstable : (prefixWord ++ tailWord_6970636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970636).length < 2 ^ (prefixWord ++ tailWord_6970636).sum := by decide
  have hdescent : baseEnd_6970636 < baseStart_6970636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970652 : List Nat := [2, 2, 3, 1, 1, 1, 4, 3, 2, 4]
def baseStart_6970652 : Nat := 118140960795 + 6970652 * 2 ^ 59
def prefixEnd_6970652 : Nat := 4983230072969 + 3 ^ 40 * 6970652 * 2
def baseEnd_6970652 : Nat := 1193098317074855508564187

theorem tailTrace_6970652 : CollatzResearch.WordTrace tailWord_6970652 prefixEnd_6970652 1193098317074855508564187 := by
  unfold tailWord_6970652
  simp only [CollatzResearch.WordTrace]
  refine ⟨127120282571262885713377105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169493710095017180951169473 127120282571262885713377105)
  ·
    refine ⟨95340211928447164285032829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127120282571262885713377105 95340211928447164285032829)
    ·
      refine ⟨35752579473167686606887311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95340211928447164285032829 35752579473167686606887311)
      ·
        refine ⟨53628869209751529910330967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35752579473167686606887311 53628869209751529910330967)
        ·
          refine ⟨80443303814627294865496451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53628869209751529910330967 80443303814627294865496451)
          ·
            refine ⟨120664955721940942298244677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80443303814627294865496451 120664955721940942298244677)
            ·
              refine ⟨22624679197863926680920877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120664955721940942298244677 22624679197863926680920877)
              ·
                refine ⟨8484254699198972505345329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22624679197863926680920877 8484254699198972505345329)
                ·
                  refine ⟨6363191024399229379008997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8484254699198972505345329 6363191024399229379008997)
                  ·
                    refine ⟨1193098317074855508564187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6363191024399229379008997 1193098317074855508564187)
                    ·
                      rfl

theorem cell23_6970652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_6970652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970652 prefixEnd_6970652 := by exact prefixLift 6970652
  have htrace : WordTrace (prefixWord ++ tailWord_6970652) baseStart_6970652 baseEnd_6970652 := by
    simpa [prefixWord, tailWord_6970652, baseEnd_6970652] using wordTrace_append hprefix tailTrace_6970652
  have hstable : (prefixWord ++ tailWord_6970652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970652).length < 2 ^ (prefixWord ++ tailWord_6970652).sum := by decide
  have hdescent : baseEnd_6970652 < baseStart_6970652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970659 : List Nat := [1, 1, 1, 4, 2, 4, 1, 2, 3, 2, 2]
def baseStart_6970659 : Nat := 118140960795 + 6970659 * 2 ^ 59
def prefixEnd_6970659 : Nat := 4983230072969 + 3 ^ 40 * 6970659 * 2
def baseEnd_6970659 : Nat := 3579298545589147998305029

theorem tailTrace_6970659 : CollatzResearch.WordTrace tailWord_6970659 prefixEnd_6970659 3579298545589147998305029 := by
  unfold tailWord_6970659
  simp only [CollatzResearch.WordTrace]
  refine ⟨254240820453500411622259031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169493880302333607748172687 254240820453500411622259031)
  ·
    refine ⟨381361230680250617433388547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254240820453500411622259031 381361230680250617433388547)
    ·
      refine ⟨572041846020375926150082821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381361230680250617433388547 572041846020375926150082821)
      ·
        refine ⟨107257846128820486153140529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 572041846020375926150082821 107257846128820486153140529)
        ·
          refine ⟨80443384596615364614855397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107257846128820486153140529 80443384596615364614855397)
          ·
            refine ⟨15083134611865380865285387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80443384596615364614855397 15083134611865380865285387)
            ·
              refine ⟨22624701917798071297928081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15083134611865380865285387 22624701917798071297928081)
              ·
                refine ⟨16968526438348553473446061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22624701917798071297928081 16968526438348553473446061)
                ·
                  refine ⟨6363197414380707552542273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16968526438348553473446061 6363197414380707552542273)
                  ·
                    refine ⟨4772398060785530664406705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6363197414380707552542273 4772398060785530664406705)
                    ·
                      refine ⟨3579298545589147998305029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4772398060785530664406705 3579298545589147998305029)
                      ·
                        rfl

theorem cell23_6970659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 3, 2, 2].length) (baseStart_6970659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970659 prefixEnd_6970659 := by exact prefixLift 6970659
  have htrace : WordTrace (prefixWord ++ tailWord_6970659) baseStart_6970659 baseEnd_6970659 := by
    simpa [prefixWord, tailWord_6970659, baseEnd_6970659] using wordTrace_append hprefix tailTrace_6970659
  have hstable : (prefixWord ++ tailWord_6970659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970659).length < 2 ^ (prefixWord ++ tailWord_6970659).sum := by decide
  have hdescent : baseEnd_6970659 < baseStart_6970659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970709 : List Nat := [1, 3, 2, 2, 3, 3, 1, 1, 1, 3, 3]
def baseStart_6970709 : Nat := 118140960795 + 6970709 * 2 ^ 59
def prefixEnd_6970709 : Nat := 4983230072969 + 3 ^ 40 * 6970709 * 2
def baseEnd_6970709 : Nat := 3579324219621872802679799

theorem tailTrace_6970709 : CollatzResearch.WordTrace tailWord_6970709 prefixEnd_6970709 3579324219621872802679799 := by
  unfold tailWord_6970709
  simp only [CollatzResearch.WordTrace]
  refine ⟨254242644103319270161579181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169495096068879513441052787 254242644103319270161579181)
  ·
    refine ⟨95340991538744726310592193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254242644103319270161579181 95340991538744726310592193)
    ·
      refine ⟨71505743654058544732944145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95340991538744726310592193 71505743654058544732944145)
      ·
        refine ⟨53629307740543908549708109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71505743654058544732944145 53629307740543908549708109)
        ·
          refine ⟨20110990402703965706140541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53629307740543908549708109 20110990402703965706140541)
          ·
            refine ⟨7541621401013987139802703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20110990402703965706140541 7541621401013987139802703)
            ·
              refine ⟨11312432101520980709704055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7541621401013987139802703 11312432101520980709704055)
              ·
                refine ⟨16968648152281471064556083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11312432101520980709704055 16968648152281471064556083)
                ·
                  refine ⟨25452972228422206596834125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16968648152281471064556083 25452972228422206596834125)
                  ·
                    refine ⟨9544864585658327473812797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25452972228422206596834125 9544864585658327473812797)
                    ·
                      refine ⟨3579324219621872802679799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9544864585658327473812797 3579324219621872802679799)
                      ·
                        rfl

theorem cell23_6970709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_6970709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970709 prefixEnd_6970709 := by exact prefixLift 6970709
  have htrace : WordTrace (prefixWord ++ tailWord_6970709) baseStart_6970709 baseEnd_6970709 := by
    simpa [prefixWord, tailWord_6970709, baseEnd_6970709] using wordTrace_append hprefix tailTrace_6970709
  have hstable : (prefixWord ++ tailWord_6970709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970709).length < 2 ^ (prefixWord ++ tailWord_6970709).sum := by decide
  have hdescent : baseEnd_6970709 < baseStart_6970709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970710 : List Nat := [5, 2, 3, 1, 1, 1, 2, 2, 1, 1, 4]
def baseStart_6970710 : Nat := 118140960795 + 6970710 * 2 ^ 59
def prefixEnd_6970710 : Nat := 4983230072969 + 3 ^ 40 * 6970710 * 2
def baseEnd_6970710 : Nat := 3579324733102527298767295

theorem tailTrace_6970710 : CollatzResearch.WordTrace tailWord_6970710 prefixEnd_6970710 3579324733102527298767295 := by
  unfold tailWord_6970710
  simp only [CollatzResearch.WordTrace]
  refine ⟨15890167536019727958272849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169495120384210431554910389 15890167536019727958272849)
  ·
    refine ⟨11917625652014795968704637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15890167536019727958272849 11917625652014795968704637)
    ·
      refine ⟨4469109619505548488264239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11917625652014795968704637 4469109619505548488264239)
      ·
        refine ⟨6703664429258322732396359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4469109619505548488264239 6703664429258322732396359)
        ·
          refine ⟨10055496643887484098594539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6703664429258322732396359 10055496643887484098594539)
          ·
            refine ⟨15083244965831226147891809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10055496643887484098594539 15083244965831226147891809)
            ·
              refine ⟨11312433724373419610918857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15083244965831226147891809 11312433724373419610918857)
              ·
                refine ⟨8484325293280064708189143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11312433724373419610918857 8484325293280064708189143)
                ·
                  refine ⟨12726487939920097062283715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8484325293280064708189143 12726487939920097062283715)
                  ·
                    refine ⟨19089731909880145593425573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12726487939920097062283715 19089731909880145593425573)
                    ·
                      refine ⟨3579324733102527298767295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19089731909880145593425573 3579324733102527298767295)
                      ·
                        rfl

theorem cell23_6970710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_6970710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970710 prefixEnd_6970710 := by exact prefixLift 6970710
  have htrace : WordTrace (prefixWord ++ tailWord_6970710) baseStart_6970710 baseEnd_6970710 := by
    simpa [prefixWord, tailWord_6970710, baseEnd_6970710] using wordTrace_append hprefix tailTrace_6970710
  have hstable : (prefixWord ++ tailWord_6970710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970710).length < 2 ^ (prefixWord ++ tailWord_6970710).sum := by decide
  have hdescent : baseEnd_6970710 < baseStart_6970710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970735 : List Nat := [1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 5]
def baseStart_6970735 : Nat := 118140960795 + 6970735 * 2 ^ 59
def prefixEnd_6970735 : Nat := 4983230072969 + 3 ^ 40 * 6970735 * 2
def baseEnd_6970735 : Nat := 3579337570118889700954679

theorem tailTrace_6970735 : CollatzResearch.WordTrace tailWord_6970735 prefixEnd_6970735 3579337570118889700954679 := by
  unfold tailWord_6970735
  simp only [CollatzResearch.WordTrace]
  refine ⟨254243592401225076602025659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169495728267483384401350439 254243592401225076602025659)
  ·
    refine ⟨381365388601837614903038489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254243592401225076602025659 381365388601837614903038489)
    ·
      refine ⟨286024041451378211177278867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381365388601837614903038489 286024041451378211177278867)
      ·
        refine ⟨429036062177067316765918301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286024041451378211177278867 429036062177067316765918301)
        ·
          refine ⟨160888523316400243787219363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 429036062177067316765918301 160888523316400243787219363)
          ·
            refine ⟨241332784974600365680829045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160888523316400243787219363 241332784974600365680829045)
            ·
              refine ⟨22624948591368784282577723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 241332784974600365680829045 22624948591368784282577723)
              ·
                refine ⟨33937422887053176423866585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22624948591368784282577723 33937422887053176423866585)
                ·
                  refine ⟨25453067165289882317899939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33937422887053176423866585 25453067165289882317899939)
                  ·
                    refine ⟨38179600747934823476849909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25453067165289882317899939 38179600747934823476849909)
                    ·
                      refine ⟨3579337570118889700954679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38179600747934823476849909 3579337570118889700954679)
                      ·
                        rfl

theorem cell23_6970735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 5].length) (baseStart_6970735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970735 prefixEnd_6970735 := by exact prefixLift 6970735
  have htrace : WordTrace (prefixWord ++ tailWord_6970735) baseStart_6970735 baseEnd_6970735 := by
    simpa [prefixWord, tailWord_6970735, baseEnd_6970735] using wordTrace_append hprefix tailTrace_6970735
  have hstable : (prefixWord ++ tailWord_6970735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970735).length < 2 ^ (prefixWord ++ tailWord_6970735).sum := by decide
  have hdescent : baseEnd_6970735 < baseStart_6970735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970745 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 4, 2, 4]
def baseStart_6970745 : Nat := 118140960795 + 6970745 * 2 ^ 59
def prefixEnd_6970745 : Nat := 4983230072969 + 3 ^ 40 * 6970745 * 2
def baseEnd_6970745 : Nat := 3579342704925434661829633

theorem tailTrace_6970745 : CollatzResearch.WordTrace tailWord_6970745 prefixEnd_6970745 3579342704925434661829633 := by
  unfold tailWord_6970745
  simp only [CollatzResearch.WordTrace]
  refine ⟨254243957131188848309889689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169495971420792565539926459 254243957131188848309889689)
  ·
    refine ⟨190682967848391636232417267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254243957131188848309889689 190682967848391636232417267)
    ·
      refine ⟨286024451772587454348625901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190682967848391636232417267 286024451772587454348625901)
      ·
        refine ⟨107259169414720295380734713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286024451772587454348625901 107259169414720295380734713)
        ·
          refine ⟨80444377061040221535551035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107259169414720295380734713 80444377061040221535551035)
          ·
            refine ⟨120666565591560332303326553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80444377061040221535551035 120666565591560332303326553)
            ·
              refine ⟨90499924193670249227494915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120666565591560332303326553 90499924193670249227494915)
              ·
                refine ⟨135749886290505373841242373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90499924193670249227494915 135749886290505373841242373)
                ·
                  refine ⟨25453103679469757595232945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135749886290505373841242373 25453103679469757595232945)
                  ·
                    refine ⟨19089827759602318196424709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25453103679469757595232945 19089827759602318196424709)
                    ·
                      refine ⟨3579342704925434661829633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19089827759602318196424709 3579342704925434661829633)
                      ·
                        rfl

theorem cell23_6970745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_6970745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970745 prefixEnd_6970745 := by exact prefixLift 6970745
  have htrace : WordTrace (prefixWord ++ tailWord_6970745) baseStart_6970745 baseEnd_6970745 := by
    simpa [prefixWord, tailWord_6970745, baseEnd_6970745] using wordTrace_append hprefix tailTrace_6970745
  have hstable : (prefixWord ++ tailWord_6970745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970745).length < 2 ^ (prefixWord ++ tailWord_6970745).sum := by decide
  have hdescent : baseEnd_6970745 < baseStart_6970745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970749 : List Nat := [1, 4, 1, 1, 2, 2, 1, 3, 4, 2, 2]
def baseStart_6970749 : Nat := 118140960795 + 6970749 * 2 ^ 59
def prefixEnd_6970749 : Nat := 4983230072969 + 3 ^ 40 * 6970749 * 2
def baseEnd_6970749 : Nat := 3579344758848052646179615

theorem tailTrace_6970749 : CollatzResearch.WordTrace tailWord_6970749 prefixEnd_6970749 3579344758848052646179615 := by
  unfold tailWord_6970749
  simp only [CollatzResearch.WordTrace]
  refine ⟨254244103023174356993035301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169496068682116237995356867 254244103023174356993035301)
  ·
    refine ⟨47670769316845191936194119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254244103023174356993035301 47670769316845191936194119)
    ·
      refine ⟨71506153975267787904291179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47670769316845191936194119 71506153975267787904291179)
      ·
        refine ⟨107259230962901681856436769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71506153975267787904291179 107259230962901681856436769)
        ·
          refine ⟨80444423222176261392327577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107259230962901681856436769 80444423222176261392327577)
          ·
            refine ⟨60333317416632196044245683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80444423222176261392327577 60333317416632196044245683)
            ·
              refine ⟨90499976124948294066368525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60333317416632196044245683 90499976124948294066368525)
              ·
                refine ⟨33937491046855610274888197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90499976124948294066368525 33937491046855610274888197)
                ·
                  refine ⟨6363279571285426926541537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33937491046855610274888197 6363279571285426926541537)
                  ·
                    refine ⟨4772459678464070194906153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6363279571285426926541537 4772459678464070194906153)
                    ·
                      refine ⟨3579344758848052646179615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4772459678464070194906153 3579344758848052646179615)
                      ·
                        rfl

theorem cell23_6970749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 4, 2, 2].length) (baseStart_6970749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970749 prefixEnd_6970749 := by exact prefixLift 6970749
  have htrace : WordTrace (prefixWord ++ tailWord_6970749) baseStart_6970749 baseEnd_6970749 := by
    simpa [prefixWord, tailWord_6970749, baseEnd_6970749] using wordTrace_append hprefix tailTrace_6970749
  have hstable : (prefixWord ++ tailWord_6970749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970749).length < 2 ^ (prefixWord ++ tailWord_6970749).sum := by decide
  have hdescent : baseEnd_6970749 < baseStart_6970749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970770 : List Nat := [3, 2, 3, 3, 1, 2, 1, 2, 1, 3, 2]
def baseStart_6970770 : Nat := 118140960795 + 6970770 * 2 ^ 59
def prefixEnd_6970770 : Nat := 4983230072969 + 3 ^ 40 * 6970770 * 2
def baseEnd_6970770 : Nat := 3579355541941797064017019

theorem tailTrace_6970770 : CollatzResearch.WordTrace tailWord_6970770 prefixEnd_6970770 3579355541941797064017019 := by
  unfold tailWord_6970770
  simp only [CollatzResearch.WordTrace]
  refine ⟨63561217239024569394887441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169496579304065518386366509 63561217239024569394887441)
  ·
    refine ⟨47670912929268427046165581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63561217239024569394887441 47670912929268427046165581)
    ·
      refine ⟨17876592348475660142312093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47670912929268427046165581 17876592348475660142312093)
      ·
        refine ⟨6703722130678372553367035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17876592348475660142312093 6703722130678372553367035)
        ·
          refine ⟨10055583196017558830050553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6703722130678372553367035 10055583196017558830050553)
          ·
            refine ⟨7541687397013169122537915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10055583196017558830050553 7541687397013169122537915)
            ·
              refine ⟨11312531095519753683806873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7541687397013169122537915 11312531095519753683806873)
              ·
                refine ⟨8484398321639815262855155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11312531095519753683806873 8484398321639815262855155)
                ·
                  refine ⟨12726597482459722894282733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8484398321639815262855155 12726597482459722894282733)
                  ·
                    refine ⟨4772474055922396085356025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12726597482459722894282733 4772474055922396085356025)
                    ·
                      refine ⟨3579355541941797064017019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4772474055922396085356025 3579355541941797064017019)
                      ·
                        rfl

theorem cell23_6970770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_6970770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970770 prefixEnd_6970770 := by exact prefixLift 6970770
  have htrace : WordTrace (prefixWord ++ tailWord_6970770) baseStart_6970770 baseEnd_6970770 := by
    simpa [prefixWord, tailWord_6970770, baseEnd_6970770] using wordTrace_append hprefix tailTrace_6970770
  have hstable : (prefixWord ++ tailWord_6970770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970770).length < 2 ^ (prefixWord ++ tailWord_6970770).sum := by decide
  have hdescent : baseEnd_6970770 < baseStart_6970770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970832 : List Nat := [2, 1, 1, 1, 1, 2, 2, 6, 3, 4]
def baseStart_6970832 : Nat := 118140960795 + 6970832 * 2 ^ 59
def prefixEnd_6970832 : Nat := 4983230072969 + 3 ^ 40 * 6970832 * 2
def baseEnd_6970832 : Nat := 1193129125914125273813911

theorem tailTrace_6970832 : CollatzResearch.WordTrace tailWord_6970832 prefixEnd_6970832 1193129125914125273813911 := by
  unfold tailWord_6970832
  simp only [CollatzResearch.WordTrace]
  refine ⟨127123565140936831084153375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169498086854582441445537833 127123565140936831084153375)
  ·
    refine ⟨190685347711405246626230063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127123565140936831084153375 190685347711405246626230063)
    ·
      refine ⟨286028021567107869939345095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190685347711405246626230063 286028021567107869939345095)
      ·
        refine ⟨429042032350661804909017643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286028021567107869939345095 429042032350661804909017643)
        ·
          refine ⟨643563048525992707363526465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429042032350661804909017643 643563048525992707363526465)
          ·
            refine ⟨482672286394494530522644849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 643563048525992707363526465 482672286394494530522644849)
            ·
              refine ⟨362004214795870897891983637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 482672286394494530522644849 362004214795870897891983637)
              ·
                refine ⟨16968947568556448338686733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 362004214795870897891983637 16968947568556448338686733)
                ·
                  refine ⟨6363355338208668127007525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16968947568556448338686733 6363355338208668127007525)
                  ·
                    refine ⟨1193129125914125273813911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6363355338208668127007525 1193129125914125273813911)
                    ·
                      rfl

theorem cell23_6970832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 3, 4].length) (baseStart_6970832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970832 prefixEnd_6970832 := by exact prefixLift 6970832
  have htrace : WordTrace (prefixWord ++ tailWord_6970832) baseStart_6970832 baseEnd_6970832 := by
    simpa [prefixWord, tailWord_6970832, baseEnd_6970832] using wordTrace_append hprefix tailTrace_6970832
  have hstable : (prefixWord ++ tailWord_6970832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970832).length < 2 ^ (prefixWord ++ tailWord_6970832).sum := by decide
  have hdescent : baseEnd_6970832 < baseStart_6970832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970836 : List Nat := [2, 4, 1, 2, 3, 2, 1, 1, 2, 5]
def baseStart_6970836 : Nat := 118140960795 + 6970836 * 2 ^ 59
def prefixEnd_6970836 : Nat := 4983230072969 + 3 ^ 40 * 6970836 * 2
def baseEnd_6970836 : Nat := 1193129810554997935263905

theorem tailTrace_6970836 : CollatzResearch.WordTrace tailWord_6970836 prefixEnd_6970836 1193129810554997935263905 := by
  unfold tailWord_6970836
  simp only [CollatzResearch.WordTrace]
  refine ⟨127123638086929585425726181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169498184115906113900968241 127123638086929585425726181)
  ·
    refine ⟨23835682141299297267323659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127123638086929585425726181 23835682141299297267323659)
    ·
      refine ⟨35753523211948945900985489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23835682141299297267323659 35753523211948945900985489)
      ·
        refine ⟨26815142408961709425739117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35753523211948945900985489 26815142408961709425739117)
        ·
          refine ⟨10055678403360641034652169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26815142408961709425739117 10055678403360641034652169)
          ·
            refine ⟨7541758802520480775989127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10055678403360641034652169 7541758802520480775989127)
            ·
              refine ⟨11312638203780721163983691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7541758802520480775989127 11312638203780721163983691)
              ·
                refine ⟨16968957305671081745975537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11312638203780721163983691 16968957305671081745975537)
                ·
                  refine ⟨12726717979253311309481653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16968957305671081745975537 12726717979253311309481653)
                  ·
                    refine ⟨1193129810554997935263905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12726717979253311309481653 1193129810554997935263905)
                    ·
                      rfl

theorem cell23_6970836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_6970836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970836 prefixEnd_6970836 := by exact prefixLift 6970836
  have htrace : WordTrace (prefixWord ++ tailWord_6970836) baseStart_6970836 baseEnd_6970836 := by
    simpa [prefixWord, tailWord_6970836, baseEnd_6970836] using wordTrace_append hprefix tailTrace_6970836
  have hstable : (prefixWord ++ tailWord_6970836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970836).length < 2 ^ (prefixWord ++ tailWord_6970836).sum := by decide
  have hdescent : baseEnd_6970836 < baseStart_6970836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970862 : List Nat := [4, 1, 2, 1, 2, 1, 3, 1, 8]
def baseStart_6970862 : Nat := 118140960795 + 6970862 * 2 ^ 59
def prefixEnd_6970862 : Nat := 4983230072969 + 3 ^ 40 * 6970862 * 2
def baseEnd_6970862 : Nat := 397711420240223411562955

theorem tailTrace_6970862 : CollatzResearch.WordTrace tailWord_6970862 prefixEnd_6970862 397711420240223411562955 := by
  unfold tailWord_6970862
  simp only [CollatzResearch.WordTrace]
  refine ⟨31781028058970622161487355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169498816314509984861265893 31781028058970622161487355)
  ·
    refine ⟨47671542088455933242231033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31781028058970622161487355 47671542088455933242231033)
    ·
      refine ⟨35753656566341949931673275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47671542088455933242231033 35753656566341949931673275)
      ·
        refine ⟨53630484849512924897509913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35753656566341949931673275 53630484849512924897509913)
        ·
          refine ⟨40222863637134693673132435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53630484849512924897509913 40222863637134693673132435)
          ·
            refine ⟨60334295455702040509698653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40222863637134693673132435 60334295455702040509698653)
            ·
              refine ⟨22625360795888265191136995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60334295455702040509698653 22625360795888265191136995)
              ·
                refine ⟨33938041193832397786705493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22625360795888265191136995 33938041193832397786705493)
                ·
                  refine ⟨397711420240223411562955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33938041193832397786705493 397711420240223411562955)
                  ·
                    rfl

theorem cell23_6970862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 8].length) (baseStart_6970862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970862 prefixEnd_6970862 := by exact prefixLift 6970862
  have htrace : WordTrace (prefixWord ++ tailWord_6970862) baseStart_6970862 baseEnd_6970862 := by
    simpa [prefixWord, tailWord_6970862, baseEnd_6970862] using wordTrace_append hprefix tailTrace_6970862
  have hstable : (prefixWord ++ tailWord_6970862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970862).length < 2 ^ (prefixWord ++ tailWord_6970862).sum := by decide
  have hdescent : baseEnd_6970862 < baseStart_6970862 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970866 : List Nat := [3, 2, 1, 4, 1, 2, 2, 1, 3, 4]
def baseStart_6970866 : Nat := 118140960795 + 6970866 * 2 ^ 59
def prefixEnd_6970866 : Nat := 4983230072969 + 3 ^ 40 * 6970866 * 2
def baseEnd_6970866 : Nat := 1193134945361542896138859

theorem tailTrace_6970866 : CollatzResearch.WordTrace tailWord_6970866 prefixEnd_6970866 1193134945361542896138859 := by
  unfold tailWord_6970866
  simp only [CollatzResearch.WordTrace]
  refine ⟨63562092590937621493761113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169498913575833657316696301 63562092590937621493761113)
  ·
    refine ⟨47671569443203216120320835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63562092590937621493761113 47671569443203216120320835)
    ·
      refine ⟨71507354164804824180481253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47671569443203216120320835 71507354164804824180481253)
      ·
        refine ⟨13407628905900904533840235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71507354164804824180481253 13407628905900904533840235)
        ·
          refine ⟨20111443358851356800760353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13407628905900904533840235 20111443358851356800760353)
          ·
            refine ⟨15083582519138517600570265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20111443358851356800760353 15083582519138517600570265)
            ·
              refine ⟨11312686889353888200427699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15083582519138517600570265 11312686889353888200427699)
              ·
                refine ⟨16969030334030832300641549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11312686889353888200427699 16969030334030832300641549)
                ·
                  refine ⟨6363386375261562112740581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16969030334030832300641549 6363386375261562112740581)
                  ·
                    refine ⟨1193134945361542896138859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6363386375261562112740581 1193134945361542896138859)
                    ·
                      rfl

theorem cell23_6970866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_6970866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970866 prefixEnd_6970866 := by exact prefixLift 6970866
  have htrace : WordTrace (prefixWord ++ tailWord_6970866) baseStart_6970866 baseEnd_6970866 := by
    simpa [prefixWord, tailWord_6970866, baseEnd_6970866] using wordTrace_append hprefix tailTrace_6970866
  have hstable : (prefixWord ++ tailWord_6970866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970866).length < 2 ^ (prefixWord ++ tailWord_6970866).sum := by decide
  have hdescent : baseEnd_6970866 < baseStart_6970866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970889 : List Nat := [1, 2, 1, 1, 3, 1, 3, 4, 3, 1, 3]
def baseStart_6970889 : Nat := 118140960795 + 6970889 * 2 ^ 59
def prefixEnd_6970889 : Nat := 4983230072969 + 3 ^ 40 * 6970889 * 2
def baseEnd_6970889 : Nat := 3579416646139682098428971

theorem tailTrace_6970889 : CollatzResearch.WordTrace tailWord_6970889 prefixEnd_6970889 3579416646139682098428971 := by
  unfold tailWord_6970889
  simp only [CollatzResearch.WordTrace]
  refine ⟨254249209242667160903131721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169499472828444773935421147 254249209242667160903131721)
  ·
    refine ⟨190686906932000370677348791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254249209242667160903131721 190686906932000370677348791)
    ·
      refine ⟨286030360398000556016023187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190686906932000370677348791 286030360398000556016023187)
      ·
        refine ⟨429045540597000834024034781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286030360398000556016023187 429045540597000834024034781)
        ·
          refine ⟨160892077723875312759013043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 429045540597000834024034781 160892077723875312759013043)
          ·
            refine ⟨241338116585812969138519565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160892077723875312759013043 241338116585812969138519565)
            ·
              refine ⟨90501793719679863426944837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241338116585812969138519565 90501793719679863426944837)
              ·
                refine ⟨16969086322439974392552157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90501793719679863426944837 16969086322439974392552157)
                ·
                  refine ⟨6363407370914990397207059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16969086322439974392552157 6363407370914990397207059)
                  ·
                    refine ⟨9545111056372485595810589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6363407370914990397207059 9545111056372485595810589)
                    ·
                      refine ⟨3579416646139682098428971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9545111056372485595810589 3579416646139682098428971)
                      ·
                        rfl

theorem cell23_6970889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 3, 1, 3].length) (baseStart_6970889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970889 prefixEnd_6970889 := by exact prefixLift 6970889
  have htrace : WordTrace (prefixWord ++ tailWord_6970889) baseStart_6970889 baseEnd_6970889 := by
    simpa [prefixWord, tailWord_6970889, baseEnd_6970889] using wordTrace_append hprefix tailTrace_6970889
  have hstable : (prefixWord ++ tailWord_6970889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970889).length < 2 ^ (prefixWord ++ tailWord_6970889).sum := by decide
  have hdescent : baseEnd_6970889 < baseStart_6970889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970899 : List Nat := [1, 1, 1, 2, 1, 6, 2, 1, 1, 5, 2]
def baseStart_6970899 : Nat := 118140960795 + 6970899 * 2 ^ 59
def prefixEnd_6970899 : Nat := 4983230072969 + 3 ^ 40 * 6970899 * 2
def baseEnd_6970899 : Nat := 3579421780946227059303925

theorem tailTrace_6970899 : CollatzResearch.WordTrace tailWord_6970899 prefixEnd_6970899 3579421780946227059303925 := by
  unfold tailWord_6970899
  simp only [CollatzResearch.WordTrace]
  refine ⟨254249573972630932610995751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169499715981753955073997167 254249573972630932610995751)
  ·
    refine ⟨381374360958946398916493627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254249573972630932610995751 381374360958946398916493627)
    ·
      refine ⟨572061541438419598374740441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381374360958946398916493627 572061541438419598374740441)
      ·
        refine ⟨429046156078814698781055331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 572061541438419598374740441 429046156078814698781055331)
        ·
          refine ⟨643569234118222048171582997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429046156078814698781055331 643569234118222048171582997)
          ·
            refine ⟨30167307849291658508042953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 643569234118222048171582997 30167307849291658508042953)
            ·
              refine ⟨22625480886968743881032215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30167307849291658508042953 22625480886968743881032215)
              ·
                refine ⟨33938221330453115821548323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22625480886968743881032215 33938221330453115821548323)
                ·
                  refine ⟨50907331995679673732322485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33938221330453115821548323 50907331995679673732322485)
                  ·
                    refine ⟨4772562374594969412405233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50907331995679673732322485 4772562374594969412405233)
                    ·
                      refine ⟨3579421780946227059303925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4772562374594969412405233 3579421780946227059303925)
                      ·
                        rfl

theorem cell23_6970899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 5, 2].length) (baseStart_6970899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970899 prefixEnd_6970899 := by exact prefixLift 6970899
  have htrace : WordTrace (prefixWord ++ tailWord_6970899) baseStart_6970899 baseEnd_6970899 := by
    simpa [prefixWord, tailWord_6970899, baseEnd_6970899] using wordTrace_append hprefix tailTrace_6970899
  have hstable : (prefixWord ++ tailWord_6970899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970899).length < 2 ^ (prefixWord ++ tailWord_6970899).sum := by decide
  have hdescent : baseEnd_6970899 < baseStart_6970899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970909 : List Nat := [1, 4, 2, 2, 1, 1, 1, 5, 1, 5]
def baseStart_6970909 : Nat := 118140960795 + 6970909 * 2 ^ 59
def prefixEnd_6970909 : Nat := 4983230072969 + 3 ^ 40 * 6970909 * 2
def baseEnd_6970909 : Nat := 1193142305250924006726293

theorem tailTrace_6970909 : CollatzResearch.WordTrace tailWord_6970909 prefixEnd_6970909 1193142305250924006726293 := by
  unfold tailWord_6970909
  simp only [CollatzResearch.WordTrace]
  refine ⟨254249938702594704318859781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169499959135063136212573187 254249938702594704318859781)
  ·
    refine ⟨47671863506736507059786209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254249938702594704318859781 47671863506736507059786209)
    ·
      refine ⟨35753897630052380294839657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47671863506736507059786209 35753897630052380294839657)
      ·
        refine ⟨26815423222539285221129743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35753897630052380294839657 26815423222539285221129743)
        ·
          refine ⟨40223134833808927831694615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26815423222539285221129743 40223134833808927831694615)
          ·
            refine ⟨60334702250713391747541923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40223134833808927831694615 60334702250713391747541923)
            ·
              refine ⟨90502053376070087621312885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60334702250713391747541923 90502053376070087621312885)
              ·
                refine ⟨8484567504006570714498083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90502053376070087621312885 8484567504006570714498083)
                ·
                  refine ⟨12726851256009856071747125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8484567504006570714498083 12726851256009856071747125)
                  ·
                    refine ⟨1193142305250924006726293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12726851256009856071747125 1193142305250924006726293)
                    ·
                      rfl

theorem cell23_6970909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_6970909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970909 prefixEnd_6970909 := by exact prefixLift 6970909
  have htrace : WordTrace (prefixWord ++ tailWord_6970909) baseStart_6970909 baseEnd_6970909 := by
    simpa [prefixWord, tailWord_6970909, baseEnd_6970909] using wordTrace_append hprefix tailTrace_6970909
  have hstable : (prefixWord ++ tailWord_6970909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970909).length < 2 ^ (prefixWord ++ tailWord_6970909).sum := by decide
  have hdescent : baseEnd_6970909 < baseStart_6970909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970949 : List Nat := [1, 3, 1, 1, 1, 4, 3, 1, 3, 2, 3]
def baseStart_6970949 : Nat := 118140960795 + 6970949 * 2 ^ 59
def prefixEnd_6970949 : Nat := 4983230072969 + 3 ^ 40 * 6970949 * 2
def baseEnd_6970949 : Nat := 3579447454978951863678695

theorem tailTrace_6970949 : CollatzResearch.WordTrace tailWord_6970949 prefixEnd_6970949 3579447454978951863678695 := by
  unfold tailWord_6970949
  simp only [CollatzResearch.WordTrace]
  refine ⟨254251397622449791150315901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169500931748299860766877267 254251397622449791150315901)
  ·
    refine ⟨95344274108418671681368463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254251397622449791150315901 95344274108418671681368463)
    ·
      refine ⟨143016411162628007522052695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95344274108418671681368463 143016411162628007522052695)
      ·
        refine ⟨214524616743942011283079043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143016411162628007522052695 214524616743942011283079043)
        ·
          refine ⟨321786925115913016924618565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214524616743942011283079043 321786925115913016924618565)
          ·
            refine ⟨60335048459233690673365981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 321786925115913016924618565 60335048459233690673365981)
            ·
              refine ⟨22625643172212634002512243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60335048459233690673365981 22625643172212634002512243)
              ·
                refine ⟨33938464758318951003768365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22625643172212634002512243 33938464758318951003768365)
                ·
                  refine ⟨12726924284369606626413137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33938464758318951003768365 12726924284369606626413137)
                  ·
                    refine ⟨9545193213277204969809853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12726924284369606626413137 9545193213277204969809853)
                    ·
                      refine ⟨3579447454978951863678695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9545193213277204969809853 3579447454978951863678695)
                      ·
                        rfl

theorem cell23_6970949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 2, 3].length) (baseStart_6970949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970949 prefixEnd_6970949 := by exact prefixLift 6970949
  have htrace : WordTrace (prefixWord ++ tailWord_6970949) baseStart_6970949 baseEnd_6970949 := by
    simpa [prefixWord, tailWord_6970949, baseEnd_6970949] using wordTrace_append hprefix tailTrace_6970949
  have hstable : (prefixWord ++ tailWord_6970949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970949).length < 2 ^ (prefixWord ++ tailWord_6970949).sum := by decide
  have hdescent : baseEnd_6970949 < baseStart_6970949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970980 : List Nat := [2, 3, 1, 1, 2, 4, 1, 4, 1, 2, 2]
def baseStart_6970980 : Nat := 118140960795 + 6970980 * 2 ^ 59
def prefixEnd_6970980 : Nat := 4983230072969 + 3 ^ 40 * 6970980 * 2
def baseEnd_6970980 : Nat := 3579463372879241242391053

theorem tailTrace_6970980 : CollatzResearch.WordTrace tailWord_6970980 prefixEnd_6970980 3579463372879241242391053 := by
  unfold tailWord_6970980
  simp only [CollatzResearch.WordTrace]
  refine ⟨127126264142668741722347197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169501685523558322296462929 127126264142668741722347197)
  ·
    refine ⟨47672349053500778145880199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127126264142668741722347197 47672349053500778145880199)
    ·
      refine ⟨71508523580251167218820299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47672349053500778145880199 71508523580251167218820299)
      ·
        refine ⟨107262785370376750828230449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71508523580251167218820299 107262785370376750828230449)
        ·
          refine ⟨80447089027782563121172837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107262785370376750828230449 80447089027782563121172837)
          ·
            refine ⟨15083829192709230585219907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80447089027782563121172837 15083829192709230585219907)
            ·
              refine ⟨22625743789063845877829861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15083829192709230585219907 22625743789063845877829861)
              ·
                refine ⟨4242326960449471102093099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22625743789063845877829861 4242326960449471102093099)
                ·
                  refine ⟨6363490440674206653139649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4242326960449471102093099 6363490440674206653139649)
                  ·
                    refine ⟨4772617830505654989854737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6363490440674206653139649 4772617830505654989854737)
                    ·
                      refine ⟨3579463372879241242391053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4772617830505654989854737 3579463372879241242391053)
                      ·
                        rfl

theorem cell23_6970980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 4, 1, 2, 2].length) (baseStart_6970980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6970980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6970980 prefixEnd_6970980 := by exact prefixLift 6970980
  have htrace : WordTrace (prefixWord ++ tailWord_6970980) baseStart_6970980 baseEnd_6970980 := by
    simpa [prefixWord, tailWord_6970980, baseEnd_6970980] using wordTrace_append hprefix tailTrace_6970980
  have hstable : (prefixWord ++ tailWord_6970980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970980).length < 2 ^ (prefixWord ++ tailWord_6970980).sum := by decide
  have hdescent : baseEnd_6970980 < baseStart_6970980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971052 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 9]
def baseStart_6971052 : Nat := 118140960795 + 6971052 * 2 ^ 59
def prefixEnd_6971052 : Nat := 4983230072969 + 3 ^ 40 * 6971052 * 2
def baseEnd_6971052 : Nat := 3579500343486364960690721

theorem tailTrace_6971052 : CollatzResearch.WordTrace tailWord_6971052 prefixEnd_6971052 3579500343486364960690721 := by
  unfold tailWord_6971052
  simp only [CollatzResearch.WordTrace]
  refine ⟨127127577170538319870657705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169503436227384426494210273 127127577170538319870657705)
  ·
    refine ⟨95345682877903739902993279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127127577170538319870657705 95345682877903739902993279)
    ·
      refine ⟨143018524316855609854489919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95345682877903739902993279 143018524316855609854489919)
      ·
        refine ⟨214527786475283414781734879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143018524316855609854489919 214527786475283414781734879)
        ·
          refine ⟨321791679712925122172602319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214527786475283414781734879 321791679712925122172602319)
          ·
            refine ⟨482687519569387683258903479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321791679712925122172602319 482687519569387683258903479)
            ·
              refine ⟨724031279354081524888355219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482687519569387683258903479 724031279354081524888355219)
              ·
                refine ⟨1086046919031122287332532829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 724031279354081524888355219 1086046919031122287332532829)
                ·
                  refine ⟨407267594636670857749699811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1086046919031122287332532829 407267594636670857749699811)
                  ·
                    refine ⟨610901391955006286624549717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 407267594636670857749699811 610901391955006286624549717)
                    ·
                      refine ⟨3579500343486364960690721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 610901391955006286624549717 3579500343486364960690721)
                      ·
                        rfl

theorem cell23_6971052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_6971052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971052 prefixEnd_6971052 := by exact prefixLift 6971052
  have htrace : WordTrace (prefixWord ++ tailWord_6971052) baseStart_6971052 baseEnd_6971052 := by
    simpa [prefixWord, tailWord_6971052, baseEnd_6971052] using wordTrace_append hprefix tailTrace_6971052
  have hstable : (prefixWord ++ tailWord_6971052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971052).length < 2 ^ (prefixWord ++ tailWord_6971052).sum := by decide
  have hdescent : baseEnd_6971052 < baseStart_6971052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971089 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 4, 5]
def baseStart_6971089 : Nat := 118140960795 + 6971089 * 2 ^ 59
def prefixEnd_6971089 : Nat := 4983230072969 + 3 ^ 40 * 6971089 * 2
def baseEnd_6971089 : Nat := 1193173114090193771976017

theorem tailTrace_6971089 : CollatzResearch.WordTrace tailWord_6971089 prefixEnd_6971089 1193173114090193771976017 := by
  unfold tailWord_6971089
  simp only [CollatzResearch.WordTrace]
  refine ⟨254256503841942595060412321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169504335894628396706941547 254256503841942595060412321)
  ·
    refine ⟨190692377881456946295309241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254256503841942595060412321 190692377881456946295309241)
    ·
      refine ⟨143019283411092709721481931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190692377881456946295309241 143019283411092709721481931)
      ·
        refine ⟨214528925116639064582222897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143019283411092709721481931 214528925116639064582222897)
        ·
          refine ⟨160896693837479298436667173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214528925116639064582222897 160896693837479298436667173)
          ·
            refine ⟨30168130094527368456875095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160896693837479298436667173 30168130094527368456875095)
            ·
              refine ⟨45252195141791052685312643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30168130094527368456875095 45252195141791052685312643)
              ·
                refine ⟨67878292712686579027968965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45252195141791052685312643 67878292712686579027968965)
                ·
                  refine ⟨12727179883628733567744181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67878292712686579027968965 12727179883628733567744181)
                  ·
                    refine ⟨1193173114090193771976017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12727179883628733567744181 1193173114090193771976017)
                    ·
                      rfl

theorem cell23_6971089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 5].length) (baseStart_6971089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971089 prefixEnd_6971089 := by exact prefixLift 6971089
  have htrace : WordTrace (prefixWord ++ tailWord_6971089) baseStart_6971089 baseEnd_6971089 := by
    simpa [prefixWord, tailWord_6971089, baseEnd_6971089] using wordTrace_append hprefix tailTrace_6971089
  have hstable : (prefixWord ++ tailWord_6971089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971089).length < 2 ^ (prefixWord ++ tailWord_6971089).sum := by decide
  have hdescent : baseEnd_6971089 < baseStart_6971089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971096 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 2, 5, 2]
def baseStart_6971096 : Nat := 118140960795 + 6971096 * 2 ^ 59
def prefixEnd_6971096 : Nat := 4983230072969 + 3 ^ 40 * 6971096 * 2
def baseEnd_6971096 : Nat := 3579522936635162788540519

theorem tailTrace_6971096 : CollatzResearch.WordTrace tailWord_6971096 prefixEnd_6971096 3579522936635162788540519 := by
  unfold tailWord_6971096
  simp only [CollatzResearch.WordTrace]
  refine ⟨127128379576458617627958571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169504506101944823503944761 127128379576458617627958571)
  ·
    refine ⟨190692569364687926441937857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127128379576458617627958571 190692569364687926441937857)
    ·
      refine ⟨143019427023515944831453393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190692569364687926441937857 143019427023515944831453393)
      ·
        refine ⟨107264570267636958623590045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143019427023515944831453393 107264570267636958623590045)
        ·
          refine ⟨40224213850363859483846267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107264570267636958623590045 40224213850363859483846267)
          ·
            refine ⟨60336320775545789225769401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40224213850363859483846267 60336320775545789225769401)
            ·
              refine ⟨45252240581659341919327051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60336320775545789225769401 45252240581659341919327051)
              ·
                refine ⟨67878360872489012878990577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45252240581659341919327051 67878360872489012878990577)
                ·
                  refine ⟨50908770654366759659242933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67878360872489012878990577 50908770654366759659242933)
                  ·
                    refine ⟨4772697248846883718054025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50908770654366759659242933 4772697248846883718054025)
                    ·
                      refine ⟨3579522936635162788540519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4772697248846883718054025 3579522936635162788540519)
                      ·
                        rfl

theorem cell23_6971096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 2, 5, 2].length) (baseStart_6971096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971096 prefixEnd_6971096 := by exact prefixLift 6971096
  have htrace : WordTrace (prefixWord ++ tailWord_6971096) baseStart_6971096 baseEnd_6971096 := by
    simpa [prefixWord, tailWord_6971096, baseEnd_6971096] using wordTrace_append hprefix tailTrace_6971096
  have hstable : (prefixWord ++ tailWord_6971096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971096).length < 2 ^ (prefixWord ++ tailWord_6971096).sum := by decide
  have hdescent : baseEnd_6971096 < baseStart_6971096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971179 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 7, 5]
def baseStart_6971179 : Nat := 118140960795 + 6971179 * 2 ^ 59
def prefixEnd_6971179 : Nat := 4983230072969 + 3 ^ 40 * 6971179 * 2
def baseEnd_6971179 : Nat := 1193188518509828654600879

theorem tailTrace_6971179 : CollatzResearch.WordTrace tailWord_6971179 prefixEnd_6971179 1193188518509828654600879 := by
  unfold tailWord_6971179
  simp only [CollatzResearch.WordTrace]
  refine ⟨254259786411616540431188591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169506524274411026954125727 254259786411616540431188591)
  ·
    refine ⟨381389679617424810646782887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254259786411616540431188591 381389679617424810646782887)
    ·
      refine ⟨572084519426137215970174331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381389679617424810646782887 572084519426137215970174331)
      ·
        refine ⟨858126779139205823955261497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572084519426137215970174331 858126779139205823955261497)
        ·
          refine ⟨643595084354404367966446123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 858126779139205823955261497 643595084354404367966446123)
          ·
            refine ⟨965392626531606551949669185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643595084354404367966446123 965392626531606551949669185)
            ·
              refine ⟨724044469898704913962251889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 965392626531606551949669185 724044469898704913962251889)
              ·
                refine ⟨543033352424028685471688917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 724044469898704913962251889 543033352424028685471688917)
                ·
                  refine ⟨12727344197438172315742709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 543033352424028685471688917 12727344197438172315742709)
                  ·
                    refine ⟨1193188518509828654600879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12727344197438172315742709 1193188518509828654600879)
                    ·
                      rfl

theorem cell23_6971179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 5].length) (baseStart_6971179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971179 prefixEnd_6971179 := by exact prefixLift 6971179
  have htrace : WordTrace (prefixWord ++ tailWord_6971179) baseStart_6971179 baseEnd_6971179 := by
    simpa [prefixWord, tailWord_6971179, baseEnd_6971179] using wordTrace_append hprefix tailTrace_6971179
  have hstable : (prefixWord ++ tailWord_6971179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971179).length < 2 ^ (prefixWord ++ tailWord_6971179).sum := by decide
  have hdescent : baseEnd_6971179 < baseStart_6971179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971210 : List Nat := [3, 1, 2, 1, 1, 1, 3, 6, 1, 1, 3]
def baseStart_6971210 : Nat := 118140960795 + 6971210 * 2 ^ 59
def prefixEnd_6971210 : Nat := 4983230072969 + 3 ^ 40 * 6971210 * 2
def baseEnd_6971210 : Nat := 3579581473429775342514995

theorem tailTrace_6971210 : CollatzResearch.WordTrace tailWord_6971210 prefixEnd_6971210 3579581473429775342514995 := by
  unfold tailWord_6971210
  simp only [CollatzResearch.WordTrace]
  refine ⟨63565229268626058181391771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169507278049669488483711389 63565229268626058181391771)
  ·
    refine ⟨95347843902939087272087657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63565229268626058181391771 95347843902939087272087657)
    ·
      refine ⟨71510882927204315454065743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95347843902939087272087657 71510882927204315454065743)
      ·
        refine ⟨107266324390806473181098615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71510882927204315454065743 107266324390806473181098615)
        ·
          refine ⟨160899486586209709771647923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107266324390806473181098615 160899486586209709771647923)
          ·
            refine ⟨241349229879314564657471885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160899486586209709771647923 241349229879314564657471885)
            ·
              refine ⟨90505961204742961746551957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241349229879314564657471885 90505961204742961746551957)
              ·
                refine ⟨4242466931472326331869623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90505961204742961746551957 4242466931472326331869623)
                ·
                  refine ⟨6363700397208489497804435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4242466931472326331869623 6363700397208489497804435)
                  ·
                    refine ⟨9545550595812734246706653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6363700397208489497804435 9545550595812734246706653)
                    ·
                      refine ⟨3579581473429775342514995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9545550595812734246706653 3579581473429775342514995)
                      ·
                        rfl

theorem cell23_6971210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 6, 1, 1, 3].length) (baseStart_6971210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971210 prefixEnd_6971210 := by exact prefixLift 6971210
  have htrace : WordTrace (prefixWord ++ tailWord_6971210) baseStart_6971210 baseEnd_6971210 := by
    simpa [prefixWord, tailWord_6971210, baseEnd_6971210] using wordTrace_append hprefix tailTrace_6971210
  have hstable : (prefixWord ++ tailWord_6971210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971210).length < 2 ^ (prefixWord ++ tailWord_6971210).sum := by decide
  have hdescent : baseEnd_6971210 < baseStart_6971210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971233 : List Nat := [1, 2, 3, 1, 1, 1, 6, 2, 1, 1, 4]
def baseStart_6971233 : Nat := 118140960795 + 6971233 * 2 ^ 59
def prefixEnd_6971233 : Nat := 4983230072969 + 3 ^ 40 * 6971233 * 2
def baseEnd_6971233 : Nat := 3579593283484828752527389

theorem tailTrace_6971233 : CollatzResearch.WordTrace tailWord_6971233 prefixEnd_6971233 3579593283484828752527389 := by
  unfold tailWord_6971233
  simp only [CollatzResearch.WordTrace]
  refine ⟨254261755953420907653654353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169507837302280605102436235 254261755953420907653654353)
  ·
    refine ⟨190696316965065680740240765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254261755953420907653654353 190696316965065680740240765)
    ·
      refine ⟨71511118861899630277590287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190696316965065680740240765 71511118861899630277590287)
      ·
        refine ⟨107266678292849445416385431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71511118861899630277590287 107266678292849445416385431)
        ·
          refine ⟨160900017439274168124578147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107266678292849445416385431 160900017439274168124578147)
          ·
            refine ⟨241350026158911252186867221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160900017439274168124578147 241350026158911252186867221)
            ·
              refine ⟨11313282476198964946259401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 241350026158911252186867221 11313282476198964946259401)
              ·
                refine ⟨8484961857149223709694551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11313282476198964946259401 8484961857149223709694551)
                ·
                  refine ⟨12727442785723835564541827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8484961857149223709694551 12727442785723835564541827)
                  ·
                    refine ⟨19091164178585753346812741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12727442785723835564541827 19091164178585753346812741)
                    ·
                      refine ⟨3579593283484828752527389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19091164178585753346812741 3579593283484828752527389)
                      ·
                        rfl

theorem cell23_6971233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_6971233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971233 prefixEnd_6971233 := by exact prefixLift 6971233
  have htrace : WordTrace (prefixWord ++ tailWord_6971233) baseStart_6971233 baseEnd_6971233 := by
    simpa [prefixWord, tailWord_6971233, baseEnd_6971233] using wordTrace_append hprefix tailTrace_6971233
  have hstable : (prefixWord ++ tailWord_6971233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971233).length < 2 ^ (prefixWord ++ tailWord_6971233).sum := by decide
  have hdescent : baseEnd_6971233 < baseStart_6971233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971253 : List Nat := [1, 3, 4, 1, 1, 1, 4, 1, 1, 1, 5]
def baseStart_6971253 : Nat := 118140960795 + 6971253 * 2 ^ 59
def prefixEnd_6971253 : Nat := 4983230072969 + 3 ^ 40 * 6971253 * 2
def baseEnd_6971253 : Nat := 3579603553097918674277297

theorem tailTrace_6971253 : CollatzResearch.WordTrace tailWord_6971253 prefixEnd_6971253 3579603553097918674277297 := by
  unfold tailWord_6971253
  simp only [CollatzResearch.WordTrace]
  refine ⟨254262485413348451069382413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169508323608898967379588275 254262485413348451069382413)
  ·
    refine ⟨95348432030005669151018405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254262485413348451069382413 95348432030005669151018405)
    ·
      refine ⟨17877831005626062965815951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95348432030005669151018405 17877831005626062965815951)
      ·
        refine ⟨26816746508439094448723927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17877831005626062965815951 26816746508439094448723927)
        ·
          refine ⟨40225119762658641673085891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26816746508439094448723927 40225119762658641673085891)
          ·
            refine ⟨60337679643987962509628837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40225119762658641673085891 60337679643987962509628837)
            ·
              refine ⟨11313314933247742970555407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60337679643987962509628837 11313314933247742970555407)
              ·
                refine ⟨16969972399871614455833111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11313314933247742970555407 16969972399871614455833111)
                ·
                  refine ⟨25454958599807421683749667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16969972399871614455833111 25454958599807421683749667)
                  ·
                    refine ⟨38182437899711132525624501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25454958599807421683749667 38182437899711132525624501)
                    ·
                      refine ⟨3579603553097918674277297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38182437899711132525624501 3579603553097918674277297)
                      ·
                        rfl

theorem cell23_6971253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_6971253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971253 prefixEnd_6971253 := by exact prefixLift 6971253
  have htrace : WordTrace (prefixWord ++ tailWord_6971253) baseStart_6971253 baseEnd_6971253 := by
    simpa [prefixWord, tailWord_6971253, baseEnd_6971253] using wordTrace_append hprefix tailTrace_6971253
  have hstable : (prefixWord ++ tailWord_6971253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971253).length < 2 ^ (prefixWord ++ tailWord_6971253).sum := by decide
  have hdescent : baseEnd_6971253 < baseStart_6971253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971267 : List Nat := [1, 1, 1, 3, 4, 4, 1, 1, 3, 2, 2]
def baseStart_6971267 : Nat := 118140960795 + 6971267 * 2 ^ 59
def prefixEnd_6971267 : Nat := 4983230072969 + 3 ^ 40 * 6971267 * 2
def baseEnd_6971267 : Nat := 3579610741827081619502233

theorem tailTrace_6971267 : CollatzResearch.WordTrace tailWord_6971267 prefixEnd_6971267 3579610741827081619502233 := by
  unfold tailWord_6971267
  simp only [CollatzResearch.WordTrace]
  refine ⟨254262996035297731460392055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169508664023531820973594703 254262996035297731460392055)
  ·
    refine ⟨381394494052946597190588083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254262996035297731460392055 381394494052946597190588083)
    ·
      refine ⟨572091741079419895785882125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381394494052946597190588083 572091741079419895785882125)
      ·
        refine ⟨214534402904782460919705797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 572091741079419895785882125 214534402904782460919705797)
        ·
          refine ⟨40225200544646711422444837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214534402904782460919705797 40225200544646711422444837)
          ·
            refine ⟨7542225102121258391708407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40225200544646711422444837 7542225102121258391708407)
            ·
              refine ⟨11313337653181887587562611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7542225102121258391708407 11313337653181887587562611)
              ·
                refine ⟨16970006479772831381343917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11313337653181887587562611 16970006479772831381343917)
                ·
                  refine ⟨6363752429914811768003969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16970006479772831381343917 6363752429914811768003969)
                  ·
                    refine ⟨4772814322436108826002977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6363752429914811768003969 4772814322436108826002977)
                    ·
                      refine ⟨3579610741827081619502233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4772814322436108826002977 3579610741827081619502233)
                      ·
                        rfl

theorem cell23_6971267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 3, 2, 2].length) (baseStart_6971267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971267 prefixEnd_6971267 := by exact prefixLift 6971267
  have htrace : WordTrace (prefixWord ++ tailWord_6971267) baseStart_6971267 baseEnd_6971267 := by
    simpa [prefixWord, tailWord_6971267, baseEnd_6971267] using wordTrace_append hprefix tailTrace_6971267
  have hstable : (prefixWord ++ tailWord_6971267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971267).length < 2 ^ (prefixWord ++ tailWord_6971267).sum := by decide
  have hdescent : baseEnd_6971267 < baseStart_6971267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971304 : List Nat := [2, 1, 6, 2, 2, 1, 1, 1, 1, 1, 5]
def baseStart_6971304 : Nat := 118140960795 + 6971304 * 2 ^ 59
def prefixEnd_6971304 : Nat := 4983230072969 + 3 ^ 40 * 6971304 * 2
def baseEnd_6971304 : Nat := 3579629740611297974739563

theorem tailTrace_6971304 : CollatzResearch.WordTrace tailWord_6971304 prefixEnd_6971304 3579629740611297974739563 := by
  unfold tailWord_6971304
  simp only [CollatzResearch.WordTrace]
  refine ⟨127132172768081843389744483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169509563690775791186325977 127132172768081843389744483)
  ·
    refine ⟨190698259152122765084616725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127132172768081843389744483 190698259152122765084616725)
    ·
      refine ⟨8938980897755754613341409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 190698259152122765084616725 8938980897755754613341409)
      ·
        refine ⟨6704235673316815960006057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8938980897755754613341409 6704235673316815960006057)
        ·
          refine ⟨5028176754987611970004543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6704235673316815960006057 5028176754987611970004543)
          ·
            refine ⟨7542265132481417955006815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5028176754987611970004543 7542265132481417955006815)
            ·
              refine ⟨11313397698722126932510223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7542265132481417955006815 11313397698722126932510223)
              ·
                refine ⟨16970096548083190398765335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11313397698722126932510223 16970096548083190398765335)
                ·
                  refine ⟨25455144822124785598148003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16970096548083190398765335 25455144822124785598148003)
                  ·
                    refine ⟨38182717233187178397222005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25455144822124785598148003 38182717233187178397222005)
                    ·
                      refine ⟨3579629740611297974739563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38182717233187178397222005 3579629740611297974739563)
                      ·
                        rfl

theorem cell23_6971304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_6971304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971304 prefixEnd_6971304 := by exact prefixLift 6971304
  have htrace : WordTrace (prefixWord ++ tailWord_6971304) baseStart_6971304 baseEnd_6971304 := by
    simpa [prefixWord, tailWord_6971304, baseEnd_6971304] using wordTrace_append hprefix tailTrace_6971304
  have hstable : (prefixWord ++ tailWord_6971304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971304).length < 2 ^ (prefixWord ++ tailWord_6971304).sum := by decide
  have hdescent : baseEnd_6971304 < baseStart_6971304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971317 : List Nat := [1, 3, 3, 2, 1, 3, 2, 2, 2, 1, 3]
def baseStart_6971317 : Nat := 118140960795 + 6971317 * 2 ^ 59
def prefixEnd_6971317 : Nat := 4983230072969 + 3 ^ 40 * 6971317 * 2
def baseEnd_6971317 : Nat := 3579636415859806423877003

theorem tailTrace_6971317 : CollatzResearch.WordTrace tailWord_6971317 prefixEnd_6971317 3579636415859806423877003 := by
  unfold tailWord_6971317
  simp only [CollatzResearch.WordTrace]
  refine ⟨254264819685116589999712205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169509879790077726666474803 254264819685116589999712205)
  ·
    refine ⟨95349307381918721249892077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254264819685116589999712205 95349307381918721249892077)
    ·
      refine ⟨35755990268219520468709529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95349307381918721249892077 35755990268219520468709529)
      ·
        refine ⟨26816992701164640351532147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35755990268219520468709529 26816992701164640351532147)
        ·
          refine ⟨40225489051746960527298221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26816992701164640351532147 40225489051746960527298221)
          ·
            refine ⟨15084558394405110197736833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40225489051746960527298221 15084558394405110197736833)
            ·
              refine ⟨11313418795803832648302625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15084558394405110197736833 11313418795803832648302625)
              ·
                refine ⟨8485064096852874486226969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11313418795803832648302625 8485064096852874486226969)
                ·
                  refine ⟨6363798072639655864670227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8485064096852874486226969 6363798072639655864670227)
                  ·
                    refine ⟨9545697108959483797005341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6363798072639655864670227 9545697108959483797005341)
                    ·
                      refine ⟨3579636415859806423877003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9545697108959483797005341 3579636415859806423877003)
                      ·
                        rfl

theorem cell23_6971317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_6971317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971317 prefixEnd_6971317 := by exact prefixLift 6971317
  have htrace : WordTrace (prefixWord ++ tailWord_6971317) baseStart_6971317 baseEnd_6971317 := by
    simpa [prefixWord, tailWord_6971317, baseEnd_6971317] using wordTrace_append hprefix tailTrace_6971317
  have hstable : (prefixWord ++ tailWord_6971317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971317).length < 2 ^ (prefixWord ++ tailWord_6971317).sum := by decide
  have hdescent : baseEnd_6971317 < baseStart_6971317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971340 : List Nat := [2, 2, 1, 4, 1, 2, 1, 3, 1, 4, 2]
def baseStart_6971340 : Nat := 118140960795 + 6971340 * 2 ^ 59
def prefixEnd_6971340 : Nat := 4983230072969 + 3 ^ 40 * 6971340 * 2
def baseEnd_6971340 : Nat := 3579648225914859833889397

theorem tailTrace_6971340 : CollatzResearch.WordTrace tailWord_6971340 prefixEnd_6971340 3579648225914859833889397 := by
  unfold tailWord_6971340
  simp only [CollatzResearch.WordTrace]
  refine ⟨127132829282016632463899737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169510439042688843285199649 127132829282016632463899737)
  ·
    refine ⟨95349621961512474347924803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127132829282016632463899737 95349621961512474347924803)
    ·
      refine ⟨143024432942268711521887205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95349621961512474347924803 143024432942268711521887205)
      ·
        refine ⟨26817081176675383410353851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143024432942268711521887205 26817081176675383410353851)
        ·
          refine ⟨40225621765013075115530777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26817081176675383410353851 40225621765013075115530777)
          ·
            refine ⟨30169216323759806336648083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40225621765013075115530777 30169216323759806336648083)
            ·
              refine ⟨45253824485639709504972125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30169216323759806336648083 45253824485639709504972125)
              ·
                refine ⟨16970184182114891064364547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45253824485639709504972125 16970184182114891064364547)
                ·
                  refine ⟨25455276273172336596546821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16970184182114891064364547 25455276273172336596546821)
                  ·
                    refine ⟨4772864301219813111852529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25455276273172336596546821 4772864301219813111852529)
                    ·
                      refine ⟨3579648225914859833889397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4772864301219813111852529 3579648225914859833889397)
                      ·
                        rfl

theorem cell23_6971340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_6971340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971340 prefixEnd_6971340 := by exact prefixLift 6971340
  have htrace : WordTrace (prefixWord ++ tailWord_6971340) baseStart_6971340 baseEnd_6971340 := by
    simpa [prefixWord, tailWord_6971340, baseEnd_6971340] using wordTrace_append hprefix tailTrace_6971340
  have hstable : (prefixWord ++ tailWord_6971340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971340).length < 2 ^ (prefixWord ++ tailWord_6971340).sum := by decide
  have hdescent : baseEnd_6971340 < baseStart_6971340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971374 : List Nat := [4, 1, 2, 1, 3, 1, 3, 2, 2, 2, 2]
def baseStart_6971374 : Nat := 118140960795 + 6971374 * 2 ^ 59
def prefixEnd_6971374 : Nat := 4983230072969 + 3 ^ 40 * 6971374 * 2
def baseEnd_6971374 : Nat := 3579665684257112700864241

theorem tailTrace_6971374 : CollatzResearch.WordTrace tailWord_6971374 prefixEnd_6971374 3579665684257112700864241 := by
  unfold tailWord_6971374
  simp only [CollatzResearch.WordTrace]
  refine ⟨31783362330738761091817147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169511265763940059156358117 31783362330738761091817147)
  ·
    refine ⟨47675043496108141637725721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31783362330738761091817147 47675043496108141637725721)
    ·
      refine ⟨35756282622081106228294291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47675043496108141637725721 35756282622081106228294291)
      ·
        refine ⟨53634423933121659342441437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35756282622081106228294291 53634423933121659342441437)
        ·
          refine ⟨20112908974920622253415539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53634423933121659342441437 20112908974920622253415539)
          ·
            refine ⟨30169363462380933380123309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20112908974920622253415539 30169363462380933380123309)
            ·
              refine ⟨11313511298392850017546241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30169363462380933380123309 11313511298392850017546241)
              ·
                refine ⟨8485133473794637513159681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11313511298392850017546241 8485133473794637513159681)
                ·
                  refine ⟨6363850105345978134869761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8485133473794637513159681 6363850105345978134869761)
                  ·
                    refine ⟨4772887579009483601152321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6363850105345978134869761 4772887579009483601152321)
                    ·
                      refine ⟨3579665684257112700864241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4772887579009483601152321 3579665684257112700864241)
                      ·
                        rfl

theorem cell23_6971374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_6971374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971374 prefixEnd_6971374 := by exact prefixLift 6971374
  have htrace : WordTrace (prefixWord ++ tailWord_6971374) baseStart_6971374 baseEnd_6971374 := by
    simpa [prefixWord, tailWord_6971374, baseEnd_6971374] using wordTrace_append hprefix tailTrace_6971374
  have hstable : (prefixWord ++ tailWord_6971374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971374).length < 2 ^ (prefixWord ++ tailWord_6971374).sum := by decide
  have hdescent : baseEnd_6971374 < baseStart_6971374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971440 : List Nat := [2, 1, 1, 1, 2, 5, 3, 1, 3, 4]
def baseStart_6971440 : Nat := 118140960795 + 6971440 * 2 ^ 59
def prefixEnd_6971440 : Nat := 4983230072969 + 3 ^ 40 * 6971440 * 2
def baseEnd_6971440 : Nat := 1193233191326769814212979

theorem tailTrace_6971440 : CollatzResearch.WordTrace tailWord_6971440 prefixEnd_6971440 1193233191326769814212979 := by
  unfold tailWord_6971440
  simp only [CollatzResearch.WordTrace]
  refine ⟨127134652931835491003219887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169512870575780654670959849 127134652931835491003219887)
  ·
    refine ⟨190701979397753236504829831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127134652931835491003219887 190701979397753236504829831)
    ·
      refine ⟨286052969096629854757244747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190701979397753236504829831 286052969096629854757244747)
      ·
        refine ⟨429079453644944782135867121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286052969096629854757244747 429079453644944782135867121)
        ·
          refine ⟨321809590233708586601900341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429079453644944782135867121 321809590233708586601900341)
          ·
            refine ⟨30169649084410179993928157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 321809590233708586601900341 30169649084410179993928157)
            ·
              refine ⟨11313618406653817497723059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30169649084410179993928157 11313618406653817497723059)
              ·
                refine ⟨16970427609980726246584589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11313618406653817497723059 16970427609980726246584589)
                ·
                  refine ⟨6363910353742772342469221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16970427609980726246584589 6363910353742772342469221)
                  ·
                    refine ⟨1193233191326769814212979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6363910353742772342469221 1193233191326769814212979)
                    ·
                      rfl

theorem cell23_6971440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 3, 4].length) (baseStart_6971440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971440 prefixEnd_6971440 := by exact prefixLift 6971440
  have htrace : WordTrace (prefixWord ++ tailWord_6971440) baseStart_6971440 baseEnd_6971440 := by
    simpa [prefixWord, tailWord_6971440, baseEnd_6971440] using wordTrace_append hprefix tailTrace_6971440
  have hstable : (prefixWord ++ tailWord_6971440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971440).length < 2 ^ (prefixWord ++ tailWord_6971440).sum := by decide
  have hdescent : baseEnd_6971440 < baseStart_6971440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971520 : List Nat := [2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 4]
def baseStart_6971520 : Nat := 118140960795 + 6971520 * 2 ^ 59
def prefixEnd_6971520 : Nat := 4983230072969 + 3 ^ 40 * 6971520 * 2
def baseEnd_6971520 : Nat := 3579740652432669129638569

theorem tailTrace_6971520 : CollatzResearch.WordTrace tailWord_6971520 prefixEnd_6971520 3579740652432669129638569 := by
  unfold tailWord_6971520
  simp only [CollatzResearch.WordTrace]
  refine ⟨127136111851690577834676007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169514815802254103779568009 127136111851690577834676007)
  ·
    refine ⟨190704167777535866752014011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127136111851690577834676007 190704167777535866752014011)
    ·
      refine ⟨286056251666303800128021017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190704167777535866752014011 286056251666303800128021017)
      ·
        refine ⟨214542188749727850096015763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286056251666303800128021017 214542188749727850096015763)
        ·
          refine ⟨321813283124591775144023645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214542188749727850096015763 321813283124591775144023645)
          ·
            refine ⟨120679981171721915679008867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 321813283124591775144023645 120679981171721915679008867)
            ·
              refine ⟨181019971757582873518513301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120679981171721915679008867 181019971757582873518513301)
              ·
                refine ⟨8485311176136697196180311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 181019971757582873518513301 8485311176136697196180311)
                ·
                  refine ⟨12727966764205045794270467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8485311176136697196180311 12727966764205045794270467)
                  ·
                    refine ⟨19091950146307568691405701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12727966764205045794270467 19091950146307568691405701)
                    ·
                      refine ⟨3579740652432669129638569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19091950146307568691405701 3579740652432669129638569)
                      ·
                        rfl

theorem cell23_6971520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 4].length) (baseStart_6971520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971520 prefixEnd_6971520 := by exact prefixLift 6971520
  have htrace : WordTrace (prefixWord ++ tailWord_6971520) baseStart_6971520 baseEnd_6971520 := by
    simpa [prefixWord, tailWord_6971520, baseEnd_6971520] using wordTrace_append hprefix tailTrace_6971520
  have hstable : (prefixWord ++ tailWord_6971520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971520).length < 2 ^ (prefixWord ++ tailWord_6971520).sum := by decide
  have hdescent : baseEnd_6971520 < baseStart_6971520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971530 : List Nat := [3, 1, 2, 3, 1, 2, 2, 2, 1, 6]
def baseStart_6971530 : Nat := 118140960795 + 6971530 * 2 ^ 59
def prefixEnd_6971530 : Nat := 4983230072969 + 3 ^ 40 * 6971530 * 2
def baseEnd_6971530 : Nat := 1193248595746404696837841

theorem tailTrace_6971530 : CollatzResearch.WordTrace tailWord_6971530 prefixEnd_6971530 1193248595746404696837841 := by
  unfold tailWord_6971530
  simp only [CollatzResearch.WordTrace]
  refine ⟨63568147108336231844304011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169515058955563284918144029 63568147108336231844304011)
  ·
    refine ⟨95352220662504347766456017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63568147108336231844304011 95352220662504347766456017)
    ·
      refine ⟨71514165496878260824842013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95352220662504347766456017 71514165496878260824842013)
      ·
        refine ⟨26817812061329347809315755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71514165496878260824842013 26817812061329347809315755)
        ·
          refine ⟨40226718091994021713973633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26817812061329347809315755 40226718091994021713973633)
          ·
            refine ⟨30170038568995516285480225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40226718091994021713973633 30170038568995516285480225)
            ·
              refine ⟨22627528926746637214110169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30170038568995516285480225 22627528926746637214110169)
              ·
                refine ⟨16970646695059977910582627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22627528926746637214110169 16970646695059977910582627)
                ·
                  refine ⟨25455970042589966865873941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16970646695059977910582627 25455970042589966865873941)
                  ·
                    refine ⟨1193248595746404696837841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25455970042589966865873941 1193248595746404696837841)
                    ·
                      rfl

theorem cell23_6971530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_6971530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971530 prefixEnd_6971530 := by exact prefixLift 6971530
  have htrace : WordTrace (prefixWord ++ tailWord_6971530) baseStart_6971530 baseEnd_6971530 := by
    simpa [prefixWord, tailWord_6971530, baseEnd_6971530] using wordTrace_append hprefix tailTrace_6971530
  have hstable : (prefixWord ++ tailWord_6971530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971530).length < 2 ^ (prefixWord ++ tailWord_6971530).sum := by decide
  have hdescent : baseEnd_6971530 < baseStart_6971530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971588 : List Nat := [2, 3, 3, 1, 2, 1, 3, 3, 1, 2, 2]
def baseStart_6971588 : Nat := 118140960795 + 6971588 * 2 ^ 59
def prefixEnd_6971588 : Nat := 4983230072969 + 3 ^ 40 * 6971588 * 2
def baseEnd_6971588 : Nat := 3579775569117174863588257

theorem tailTrace_6971588 : CollatzResearch.WordTrace tailWord_6971588 prefixEnd_6971588 3579775569117174863588257 := by
  unfold tailWord_6971588
  simp only [CollatzResearch.WordTrace]
  refine ⟨127137351933567401641413709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169516469244756535521884945 127137351933567401641413709)
  ·
    refine ⟨47676506975087775615530141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127137351933567401641413709 47676506975087775615530141)
    ·
      refine ⟨17878690115657915855823803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47676506975087775615530141 17878690115657915855823803)
      ·
        refine ⟨26818035173486873783735705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17878690115657915855823803 26818035173486873783735705)
        ·
          refine ⟨20113526380115155337801779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26818035173486873783735705 20113526380115155337801779)
          ·
            refine ⟨30170289570172733006702669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20113526380115155337801779 30170289570172733006702669)
            ·
              refine ⟨11313858588814774877513501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30170289570172733006702669 11313858588814774877513501)
              ·
                refine ⟨4242696970805540579067563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11313858588814774877513501 4242696970805540579067563)
                ·
                  refine ⟨6364045456208310868601345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4242696970805540579067563 6364045456208310868601345)
                  ·
                    refine ⟨4773034092156233151451009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6364045456208310868601345 4773034092156233151451009)
                    ·
                      refine ⟨3579775569117174863588257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4773034092156233151451009 3579775569117174863588257)
                      ·
                        rfl

theorem cell23_6971588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_6971588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971588 prefixEnd_6971588 := by exact prefixLift 6971588
  have htrace : WordTrace (prefixWord ++ tailWord_6971588) baseStart_6971588 baseEnd_6971588 := by
    simpa [prefixWord, tailWord_6971588, baseEnd_6971588] using wordTrace_append hprefix tailTrace_6971588
  have hstable : (prefixWord ++ tailWord_6971588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971588).length < 2 ^ (prefixWord ++ tailWord_6971588).sum := by decide
  have hdescent : baseEnd_6971588 < baseStart_6971588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971605 : List Nat := [1, 3, 2, 4, 2, 1, 3, 2, 1, 2, 2]
def baseStart_6971605 : Nat := 118140960795 + 6971605 * 2 ^ 59
def prefixEnd_6971605 : Nat := 4983230072969 + 3 ^ 40 * 6971605 * 2
def baseEnd_6971605 : Nat := 3579784298288301297075679

theorem tailTrace_6971605 : CollatzResearch.WordTrace tailWord_6971605 prefixEnd_6971605 3579784298288301297075679 := by
  unfold tailWord_6971605
  simp only [CollatzResearch.WordTrace]
  refine ⟨254275323908073215186196269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169516882605382143457464179 254275323908073215186196269)
  ·
    refine ⟨95353246465527455694823601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254275323908073215186196269 95353246465527455694823601)
    ·
      refine ⟨71514934849145591771117701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95353246465527455694823601 71514934849145591771117701)
      ·
        refine ⟨13409050284214798457084569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71514934849145591771117701 13409050284214798457084569)
        ·
          refine ⟨10056787713161098842813427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13409050284214798457084569 10056787713161098842813427)
          ·
            refine ⟨15085181569741648264220141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10056787713161098842813427 15085181569741648264220141)
            ·
              refine ⟨5656943088653118099082553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15085181569741648264220141 5656943088653118099082553)
              ·
                refine ⟨4242707316489838574311915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5656943088653118099082553 4242707316489838574311915)
                ·
                  refine ⟨6364060974734757861467873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4242707316489838574311915 6364060974734757861467873)
                  ·
                    refine ⟨4773045731051068396100905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6364060974734757861467873 4773045731051068396100905)
                    ·
                      refine ⟨3579784298288301297075679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4773045731051068396100905 3579784298288301297075679)
                      ·
                        rfl

theorem cell23_6971605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_6971605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971605 prefixEnd_6971605 := by exact prefixLift 6971605
  have htrace : WordTrace (prefixWord ++ tailWord_6971605) baseStart_6971605 baseEnd_6971605 := by
    simpa [prefixWord, tailWord_6971605, baseEnd_6971605] using wordTrace_append hprefix tailTrace_6971605
  have hstable : (prefixWord ++ tailWord_6971605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971605).length < 2 ^ (prefixWord ++ tailWord_6971605).sum := by decide
  have hdescent : baseEnd_6971605 < baseStart_6971605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971621 : List Nat := [1, 3, 1, 4, 2, 1, 4, 1, 2, 1, 3]
def baseStart_6971621 : Nat := 118140960795 + 6971621 * 2 ^ 59
def prefixEnd_6971621 : Nat := 4983230072969 + 3 ^ 40 * 6971621 * 2
def baseEnd_6971621 : Nat := 3579792513978773234475605

theorem tailTrace_6971621 : CollatzResearch.WordTrace tailWord_6971621 prefixEnd_6971621 3579792513978773234475605 := by
  unfold tailWord_6971621
  simp only [CollatzResearch.WordTrace]
  refine ⟨254275907476015249918778717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169517271650676833279185811 254275907476015249918778717)
  ·
    refine ⟨95353465303505718719542019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254275907476015249918778717 95353465303505718719542019)
    ·
      refine ⟨143030197955258578079313029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95353465303505718719542019 143030197955258578079313029)
      ·
        refine ⟨26818162116610983389871193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143030197955258578079313029 26818162116610983389871193)
        ·
          refine ⟨20113621587458237542403395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26818162116610983389871193 20113621587458237542403395)
          ·
            refine ⟨30170432381187356313605093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20113621587458237542403395 30170432381187356313605093)
            ·
              refine ⟨5656956071472629308800955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30170432381187356313605093 5656956071472629308800955)
              ·
                refine ⟨8485434107208943963201433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5656956071472629308800955 8485434107208943963201433)
                ·
                  refine ⟨6364075580406707972401075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8485434107208943963201433 6364075580406707972401075)
                  ·
                    refine ⟨9546113370610061958601613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6364075580406707972401075 9546113370610061958601613)
                    ·
                      refine ⟨3579792513978773234475605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9546113370610061958601613 3579792513978773234475605)
                      ·
                        rfl

theorem cell23_6971621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_6971621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971621 prefixEnd_6971621 := by exact prefixLift 6971621
  have htrace : WordTrace (prefixWord ++ tailWord_6971621) baseStart_6971621 baseEnd_6971621 := by
    simpa [prefixWord, tailWord_6971621, baseEnd_6971621] using wordTrace_append hprefix tailTrace_6971621
  have hstable : (prefixWord ++ tailWord_6971621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971621).length < 2 ^ (prefixWord ++ tailWord_6971621).sum := by decide
  have hdescent : baseEnd_6971621 < baseStart_6971621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971627 : List Nat := [1, 1, 1, 1, 2, 5, 2, 3, 1, 4, 2]
def baseStart_6971627 : Nat := 118140960795 + 6971627 * 2 ^ 59
def prefixEnd_6971627 : Nat := 4983230072969 + 3 ^ 40 * 6971627 * 2
def baseEnd_6971627 : Nat := 3579795594862700211000577

theorem tailTrace_6971627 : CollatzResearch.WordTrace tailWord_6971627 prefixEnd_6971627 3579795594862700211000577 := by
  unfold tailWord_6971627
  simp only [CollatzResearch.WordTrace]
  refine ⟨254276126313993512943497135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169517417542662341962331423 254276126313993512943497135)
  ·
    refine ⟨381414189470990269415245703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254276126313993512943497135 381414189470990269415245703)
    ·
      refine ⟨572121284206485404122868555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381414189470990269415245703 572121284206485404122868555)
      ·
        refine ⟨858181926309728106184302833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572121284206485404122868555 858181926309728106184302833)
        ·
          refine ⟨643636444732296079638227125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 858181926309728106184302833 643636444732296079638227125)
          ·
            refine ⟨60340916693652757466083793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 643636444732296079638227125 60340916693652757466083793)
            ·
              refine ⟨45255687520239568099562845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60340916693652757466083793 45255687520239568099562845)
              ·
                refine ⟨16970882820089838037336067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45255687520239568099562845 16970882820089838037336067)
                ·
                  refine ⟨25456324230134757056004101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16970882820089838037336067 25456324230134757056004101)
                  ·
                    refine ⟨4773060793150266948000769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25456324230134757056004101 4773060793150266948000769)
                    ·
                      refine ⟨3579795594862700211000577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4773060793150266948000769 3579795594862700211000577)
                      ·
                        rfl

theorem cell23_6971627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 4, 2].length) (baseStart_6971627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971627 prefixEnd_6971627 := by exact prefixLift 6971627
  have htrace : WordTrace (prefixWord ++ tailWord_6971627) baseStart_6971627 baseEnd_6971627 := by
    simpa [prefixWord, tailWord_6971627, baseEnd_6971627] using wordTrace_append hprefix tailTrace_6971627
  have hstable : (prefixWord ++ tailWord_6971627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971627).length < 2 ^ (prefixWord ++ tailWord_6971627).sum := by decide
  have hdescent : baseEnd_6971627 < baseStart_6971627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971631 : List Nat := [1, 1, 2, 1, 6, 3, 1, 2, 1, 3, 2]
def baseStart_6971631 : Nat := 118140960795 + 6971631 * 2 ^ 59
def prefixEnd_6971631 : Nat := 4983230072969 + 3 ^ 40 * 6971631 * 2
def baseEnd_6971631 : Nat := 3579797648785318195350559

theorem tailTrace_6971631 : CollatzResearch.WordTrace tailWord_6971631 prefixEnd_6971631 3579797648785318195350559 := by
  unfold tailWord_6971631
  simp only [CollatzResearch.WordTrace]
  refine ⟨254276272205979021626642747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169517514803986014417761831 254276272205979021626642747)
  ·
    refine ⟨381414408308968532439964121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254276272205979021626642747 381414408308968532439964121)
    ·
      refine ⟨286060806231726399329973091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381414408308968532439964121 286060806231726399329973091)
      ·
        refine ⟨429091209347589598994959637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286060806231726399329973091 429091209347589598994959637)
        ·
          refine ⟨20113650438168262452888733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 429091209347589598994959637 20113650438168262452888733)
          ·
            refine ⟨7542618914313098419833275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20113650438168262452888733 7542618914313098419833275)
            ·
              refine ⟨11313928371469647629749913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7542618914313098419833275 11313928371469647629749913)
              ·
                refine ⟨8485446278602235722312435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11313928371469647629749913 8485446278602235722312435)
                ·
                  refine ⟨12728169417903353583468653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8485446278602235722312435 12728169417903353583468653)
                  ·
                    refine ⟨4773063531713757593800745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12728169417903353583468653 4773063531713757593800745)
                    ·
                      refine ⟨3579797648785318195350559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4773063531713757593800745 3579797648785318195350559)
                      ·
                        rfl

theorem cell23_6971631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 3, 2].length) (baseStart_6971631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971631 prefixEnd_6971631 := by exact prefixLift 6971631
  have htrace : WordTrace (prefixWord ++ tailWord_6971631) baseStart_6971631 baseEnd_6971631 := by
    simpa [prefixWord, tailWord_6971631, baseEnd_6971631] using wordTrace_append hprefix tailTrace_6971631
  have hstable : (prefixWord ++ tailWord_6971631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971631).length < 2 ^ (prefixWord ++ tailWord_6971631).sum := by decide
  have hdescent : baseEnd_6971631 < baseStart_6971631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971644 : List Nat := [2, 2, 2, 1, 4, 2, 1, 2, 1, 4, 2]
def baseStart_6971644 : Nat := 118140960795 + 6971644 * 2 ^ 59
def prefixEnd_6971644 : Nat := 4983230072969 + 3 ^ 40 * 6971644 * 2
def baseEnd_6971644 : Nat := 3579804324033826644487999

theorem tailTrace_6971644 : CollatzResearch.WordTrace tailWord_6971644 prefixEnd_6971644 3579804324033826644487999 := by
  unfold tailWord_6971644
  simp only [CollatzResearch.WordTrace]
  refine ⟨127138373177465962423432993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169517830903287949897910657 127138373177465962423432993)
  ·
    refine ⟨95353779883099471817574745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127138373177465962423432993 95353779883099471817574745)
    ·
      refine ⟨71515334912324603863181059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95353779883099471817574745 71515334912324603863181059)
      ·
        refine ⟨107273002368486905794771589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71515334912324603863181059 107273002368486905794771589)
        ·
          refine ⟨20113687944091294836519673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107273002368486905794771589 20113687944091294836519673)
          ·
            refine ⟨15085265958068471127389755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20113687944091294836519673 15085265958068471127389755)
            ·
              refine ⟨22627898937102706691084633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15085265958068471127389755 22627898937102706691084633)
              ·
                refine ⟨16970924202827030018313475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22627898937102706691084633 16970924202827030018313475)
                ·
                  refine ⟨25456386304240545027470213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16970924202827030018313475 25456386304240545027470213)
                  ·
                    refine ⟨4773072432045102192650665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25456386304240545027470213 4773072432045102192650665)
                    ·
                      refine ⟨3579804324033826644487999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4773072432045102192650665 3579804324033826644487999)
                      ·
                        rfl

theorem cell23_6971644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 1, 4, 2].length) (baseStart_6971644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971644 prefixEnd_6971644 := by exact prefixLift 6971644
  have htrace : WordTrace (prefixWord ++ tailWord_6971644) baseStart_6971644 baseEnd_6971644 := by
    simpa [prefixWord, tailWord_6971644, baseEnd_6971644] using wordTrace_append hprefix tailTrace_6971644
  have hstable : (prefixWord ++ tailWord_6971644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971644).length < 2 ^ (prefixWord ++ tailWord_6971644).sum := by decide
  have hdescent : baseEnd_6971644 < baseStart_6971644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971678 : List Nat := [4, 3, 2, 1, 1, 2, 2, 1, 1, 4, 2]
def baseStart_6971678 : Nat := 118140960795 + 6971678 * 2 ^ 59
def prefixEnd_6971678 : Nat := 4983230072969 + 3 ^ 40 * 6971678 * 2
def baseEnd_6971678 : Nat := 3579821782376079511462843

theorem tailTrace_6971678 : CollatzResearch.WordTrace tailWord_6971678 prefixEnd_6971678 3579821782376079511462843 := by
  unfold tailWord_6971678
  simp only [CollatzResearch.WordTrace]
  refine ⟨31784748304601093581700461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169518657624539165769069125 31784748304601093581700461)
  ·
    refine ⟨11919280614225410093137673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31784748304601093581700461 11919280614225410093137673)
    ·
      refine ⟨8939460460669057569853255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11919280614225410093137673 8939460460669057569853255)
      ·
        refine ⟨13409190691003586354779883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8939460460669057569853255 13409190691003586354779883)
        ·
          refine ⟨20113786036505379532169825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13409190691003586354779883 20113786036505379532169825)
          ·
            refine ⟨15085339527379034649127369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20113786036505379532169825 15085339527379034649127369)
            ·
              refine ⟨11314004645534275986845527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15085339527379034649127369 11314004645534275986845527)
              ·
                refine ⟨16971006968301413980268291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11314004645534275986845527 16971006968301413980268291)
                ·
                  refine ⟨25456510452452120970402437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16971006968301413980268291 25456510452452120970402437)
                  ·
                    refine ⟨4773095709834772681950457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25456510452452120970402437 4773095709834772681950457)
                    ·
                      refine ⟨3579821782376079511462843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4773095709834772681950457 3579821782376079511462843)
                      ·
                        rfl

theorem cell23_6971678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_6971678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971678 prefixEnd_6971678 := by exact prefixLift 6971678
  have htrace : WordTrace (prefixWord ++ tailWord_6971678) baseStart_6971678 baseEnd_6971678 := by
    simpa [prefixWord, tailWord_6971678, baseEnd_6971678] using wordTrace_append hprefix tailTrace_6971678
  have hstable : (prefixWord ++ tailWord_6971678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971678).length < 2 ^ (prefixWord ++ tailWord_6971678).sum := by decide
  have hdescent : baseEnd_6971678 < baseStart_6971678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971697 : List Nat := [1, 2, 2, 3, 4, 1, 1, 1, 1, 7]
def baseStart_6971697 : Nat := 118140960795 + 6971697 * 2 ^ 59
def prefixEnd_6971697 : Nat := 4983230072969 + 3 ^ 40 * 6971697 * 2
def baseEnd_6971697 : Nat := 1193277179502838312375085

theorem tailTrace_6971697 : CollatzResearch.WordTrace tailWord_6971697 prefixEnd_6971697 1193277179502838312375085 := by
  unfold tailWord_6971697
  simp only [CollatzResearch.WordTrace]
  refine ⟨254278679423739914898545345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169519119615826609932363563 254278679423739914898545345)
  ·
    refine ⟨190709009567804936173909009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254278679423739914898545345 190709009567804936173909009)
    ·
      refine ⟨143031757175853702130431757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190709009567804936173909009 143031757175853702130431757)
      ·
        refine ⟨53636908940945138298911909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143031757175853702130431757 53636908940945138298911909)
        ·
          refine ⟨10056920426427213431045983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53636908940945138298911909 10056920426427213431045983)
          ·
            refine ⟨15085380639640820146568975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10056920426427213431045983 15085380639640820146568975)
            ·
              refine ⟨22628070959461230219853463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15085380639640820146568975 22628070959461230219853463)
              ·
                refine ⟨33942106439191845329780195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22628070959461230219853463 33942106439191845329780195)
                ·
                  refine ⟨50913159658787767994670293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33942106439191845329780195 50913159658787767994670293)
                  ·
                    refine ⟨1193277179502838312375085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50913159658787767994670293 1193277179502838312375085)
                    ·
                      rfl

theorem cell23_6971697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 7].length) (baseStart_6971697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971697 prefixEnd_6971697 := by exact prefixLift 6971697
  have htrace : WordTrace (prefixWord ++ tailWord_6971697) baseStart_6971697 baseEnd_6971697 := by
    simpa [prefixWord, tailWord_6971697, baseEnd_6971697] using wordTrace_append hprefix tailTrace_6971697
  have hstable : (prefixWord ++ tailWord_6971697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971697).length < 2 ^ (prefixWord ++ tailWord_6971697).sum := by decide
  have hdescent : baseEnd_6971697 < baseStart_6971697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971720 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 2, 3, 5]
def baseStart_6971720 : Nat := 118140960795 + 6971720 * 2 ^ 59
def prefixEnd_6971720 : Nat := 4983230072969 + 3 ^ 40 * 6971720 * 2
def baseEnd_6971720 : Nat := 3579843348563568347137649

theorem tailTrace_6971720 : CollatzResearch.WordTrace tailWord_6971720 prefixEnd_6971720 3579843348563568347137649 := by
  unfold tailWord_6971720
  simp only [CollatzResearch.WordTrace]
  refine ⟨127139759151328294913316307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169519678868437726551088409 127139759151328294913316307)
  ·
    refine ⟨190709638726992442369974461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127139759151328294913316307 190709638726992442369974461)
    ·
      refine ⟨71516114522622165888740423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190709638726992442369974461 71516114522622165888740423)
      ·
        refine ⟨107274171783933248833110635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71516114522622165888740423 107274171783933248833110635)
        ·
          refine ⟨160911257675899873249665953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107274171783933248833110635 160911257675899873249665953)
          ·
            refine ⟨120683443256924904937249465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160911257675899873249665953 120683443256924904937249465)
            ·
              refine ⟨90512582442693678702937099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120683443256924904937249465 90512582442693678702937099)
              ·
                refine ⟨135768873664040518054405649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90512582442693678702937099 135768873664040518054405649)
                ·
                  refine ⟨101826655248030388540804237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135768873664040518054405649 101826655248030388540804237)
                  ·
                    refine ⟨38184995718011395702801589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101826655248030388540804237 38184995718011395702801589)
                    ·
                      refine ⟨3579843348563568347137649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38184995718011395702801589 3579843348563568347137649)
                      ·
                        rfl

theorem cell23_6971720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_6971720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971720 prefixEnd_6971720 := by exact prefixLift 6971720
  have htrace : WordTrace (prefixWord ++ tailWord_6971720) baseStart_6971720 baseEnd_6971720 := by
    simpa [prefixWord, tailWord_6971720, baseEnd_6971720] using wordTrace_append hprefix tailTrace_6971720
  have hstable : (prefixWord ++ tailWord_6971720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971720).length < 2 ^ (prefixWord ++ tailWord_6971720).sum := by decide
  have hdescent : baseEnd_6971720 < baseStart_6971720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971754 : List Nat := [3, 1, 3, 3, 1, 1, 2, 1, 1, 4, 3]
def baseStart_6971754 : Nat := 118140960795 + 6971754 * 2 ^ 59
def prefixEnd_6971754 : Nat := 4983230072969 + 3 ^ 40 * 6971754 * 2
def baseEnd_6971754 : Nat := 3579860806905821214112493

theorem tailTrace_6971754 : CollatzResearch.WordTrace tailWord_6971754 prefixEnd_6971754 3579860806905821214112493 := by
  unfold tailWord_6971754
  simp only [CollatzResearch.WordTrace]
  refine ⟨63570189596133353408342579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169520505589688942422246877 63570189596133353408342579)
  ·
    refine ⟨95355284394200030112513869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63570189596133353408342579 95355284394200030112513869)
    ·
      refine ⟨35758231647825011292192701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95355284394200030112513869 35758231647825011292192701)
      ·
        refine ⟨13409336867934379234572263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35758231647825011292192701 13409336867934379234572263)
        ·
          refine ⟨20114005301901568851858395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13409336867934379234572263 20114005301901568851858395)
          ·
            refine ⟨30171007952852353277787593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20114005301901568851858395 30171007952852353277787593)
            ·
              refine ⟨22628255964639264958340695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30171007952852353277787593 22628255964639264958340695)
              ·
                refine ⟨33942383946958897437511043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22628255964639264958340695 33942383946958897437511043)
                ·
                  refine ⟨50913575920438346156266565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33942383946958897437511043 50913575920438346156266565)
                  ·
                    refine ⟨9546295485082189904299981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50913575920438346156266565 9546295485082189904299981)
                    ·
                      refine ⟨3579860806905821214112493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9546295485082189904299981 3579860806905821214112493)
                      ·
                        rfl

theorem cell23_6971754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_6971754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971754 prefixEnd_6971754 := by exact prefixLift 6971754
  have htrace : WordTrace (prefixWord ++ tailWord_6971754) baseStart_6971754 baseEnd_6971754 := by
    simpa [prefixWord, tailWord_6971754, baseEnd_6971754] using wordTrace_append hprefix tailTrace_6971754
  have hstable : (prefixWord ++ tailWord_6971754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971754).length < 2 ^ (prefixWord ++ tailWord_6971754).sum := by decide
  have hdescent : baseEnd_6971754 < baseStart_6971754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971811 : List Nat := [1, 1, 1, 4, 1, 5, 2, 1, 2, 3, 2]
def baseStart_6971811 : Nat := 118140960795 + 6971811 * 2 ^ 59
def prefixEnd_6971811 : Nat := 4983230072969 + 3 ^ 40 * 6971811 * 2
def baseEnd_6971811 : Nat := 3579890075303127491099731

theorem tailTrace_6971811 : CollatzResearch.WordTrace tailWord_6971811 prefixEnd_6971811 3579890075303127491099731 := by
  unfold tailWord_6971811
  simp only [CollatzResearch.WordTrace]
  refine ⟨254282837345326912368195287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169521891563551274912130191 254282837345326912368195287)
  ·
    refine ⟨381424256017990368552292931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254282837345326912368195287 381424256017990368552292931)
    ·
      refine ⟨572136384026985552828439397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381424256017990368552292931 572136384026985552828439397)
      ·
        refine ⟨107275572005059791155332387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 572136384026985552828439397 107275572005059791155332387)
        ·
          refine ⟨160913358007589686732998581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107275572005059791155332387 160913358007589686732998581)
          ·
            refine ⟨15085627313211533131218617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160913358007589686732998581 15085627313211533131218617)
            ·
              refine ⟨11314220484908649848413963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15085627313211533131218617 11314220484908649848413963)
              ·
                refine ⟨16971330727362974772620945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11314220484908649848413963 16971330727362974772620945)
                ·
                  refine ⟨12728498045522231079465709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16971330727362974772620945 12728498045522231079465709)
                  ·
                    refine ⟨4773186767070836654799641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12728498045522231079465709 4773186767070836654799641)
                    ·
                      refine ⟨3579890075303127491099731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4773186767070836654799641 3579890075303127491099731)
                      ·
                        rfl

theorem cell23_6971811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 3, 2].length) (baseStart_6971811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971811 prefixEnd_6971811 := by exact prefixLift 6971811
  have htrace : WordTrace (prefixWord ++ tailWord_6971811) baseStart_6971811 baseEnd_6971811 := by
    simpa [prefixWord, tailWord_6971811, baseEnd_6971811] using wordTrace_append hprefix tailTrace_6971811
  have hstable : (prefixWord ++ tailWord_6971811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971811).length < 2 ^ (prefixWord ++ tailWord_6971811).sum := by decide
  have hdescent : baseEnd_6971811 < baseStart_6971811 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971817 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 6, 4]
def baseStart_6971817 : Nat := 118140960795 + 6971817 * 2 ^ 59
def prefixEnd_6971817 : Nat := 4983230072969 + 3 ^ 40 * 6971817 * 2
def baseEnd_6971817 : Nat := 1193297718729018155874901

theorem tailTrace_6971817 : CollatzResearch.WordTrace tailWord_6971817 prefixEnd_6971817 1193297718729018155874901 := by
  unfold tailWord_6971817
  simp only [CollatzResearch.WordTrace]
  refine ⟨254283056183305175392913705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169522037455536783595275803 254283056183305175392913705)
  ·
    refine ⟨190712292137478881544685279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254283056183305175392913705 190712292137478881544685279)
    ·
      refine ⟨286068438206218322317027919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190712292137478881544685279 286068438206218322317027919)
      ·
        refine ⟨429102657309327483475541879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286068438206218322317027919 429102657309327483475541879)
        ·
          refine ⟨643653985963991225213312819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429102657309327483475541879 643653985963991225213312819)
          ·
            refine ⟨965480978945986837819969229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643653985963991225213312819 965480978945986837819969229)
            ·
              refine ⟨362055367104745064182488461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 965480978945986837819969229 362055367104745064182488461)
              ·
                refine ⟨135770762664279399068433173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 362055367104745064182488461 135770762664279399068433173)
                ·
                  refine ⟨6364254499888096831332805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135770762664279399068433173 6364254499888096831332805)
                  ·
                    refine ⟨1193297718729018155874901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6364254499888096831332805 1193297718729018155874901)
                    ·
                      rfl

theorem cell23_6971817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 6, 4].length) (baseStart_6971817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971817 prefixEnd_6971817 := by exact prefixLift 6971817
  have htrace : WordTrace (prefixWord ++ tailWord_6971817) baseStart_6971817 baseEnd_6971817 := by
    simpa [prefixWord, tailWord_6971817, baseEnd_6971817] using wordTrace_append hprefix tailTrace_6971817
  have hstable : (prefixWord ++ tailWord_6971817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971817).length < 2 ^ (prefixWord ++ tailWord_6971817).sum := by decide
  have hdescent : baseEnd_6971817 < baseStart_6971817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971847 : List Nat := [1, 1, 4, 1, 1, 4, 3, 8]
def baseStart_6971847 : Nat := 118140960795 + 6971847 * 2 ^ 59
def prefixEnd_6971847 : Nat := 4983230072969 + 3 ^ 40 * 6971847 * 2
def baseEnd_6971847 : Nat := 132589205948395901861095

theorem tailTrace_6971847 : CollatzResearch.WordTrace tailWord_6971847 prefixEnd_6971847 132589205948395901861095 := by
  unfold tailWord_6971847
  simp only [CollatzResearch.WordTrace]
  refine ⟨254284150373196490516505795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169522766915464327011003863 254284150373196490516505795)
  ·
    refine ⟨381426225559794735774758693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254284150373196490516505795 381426225559794735774758693)
    ·
      refine ⟨71517417292461512957767255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 381426225559794735774758693 71517417292461512957767255)
      ·
        refine ⟨107276125938692269436650883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71517417292461512957767255 107276125938692269436650883)
        ·
          refine ⟨160914188908038404154976325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107276125938692269436650883 160914188908038404154976325)
          ·
            refine ⟨30171410420257200779058061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160914188908038404154976325 30171410420257200779058061)
            ·
              refine ⟨11314278907596450292146773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30171410420257200779058061 11314278907596450292146773)
              ·
                refine ⟨132589205948395901861095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11314278907596450292146773 132589205948395901861095)
                ·
                  rfl

theorem cell23_6971847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 8].length) (baseStart_6971847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971847 prefixEnd_6971847 := by exact prefixLift 6971847
  have htrace : WordTrace (prefixWord ++ tailWord_6971847) baseStart_6971847 baseEnd_6971847 := by
    simpa [prefixWord, tailWord_6971847, baseEnd_6971847] using wordTrace_append hprefix tailTrace_6971847
  have hstable : (prefixWord ++ tailWord_6971847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971847).length < 2 ^ (prefixWord ++ tailWord_6971847).sum := by decide
  have hdescent : baseEnd_6971847 < baseStart_6971847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971875 : List Nat := [1, 1, 1, 6, 4, 1, 2, 1, 1, 1, 4]
def baseStart_6971875 : Nat := 118140960795 + 6971875 * 2 ^ 59
def prefixEnd_6971875 : Nat := 4983230072969 + 3 ^ 40 * 6971875 * 2
def baseEnd_6971875 : Nat := 3579922938065015240699437

theorem tailTrace_6971875 : CollatzResearch.WordTrace tailWord_6971875 prefixEnd_6971875 3579922938065015240699437 := by
  unfold tailWord_6971875
  simp only [CollatzResearch.WordTrace]
  refine ⟨254285171617095051298525079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169523447744730034199016719 254285171617095051298525079)
  ·
    refine ⟨381427757425642576947787619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254285171617095051298525079 381427757425642576947787619)
    ·
      refine ⟨572141636138463865421681429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381427757425642576947787619 572141636138463865421681429)
      ·
        refine ⟨26819139193990493691641317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 572141636138463865421681429 26819139193990493691641317)
        ·
          refine ⟨5028588598873217567182747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26819139193990493691641317 5028588598873217567182747)
          ·
            refine ⟨7542882898309826350774121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5028588598873217567182747 7542882898309826350774121)
            ·
              refine ⟨5657162173732369763080591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7542882898309826350774121 5657162173732369763080591)
              ·
                refine ⟨8485743260598554644620887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5657162173732369763080591 8485743260598554644620887)
                ·
                  refine ⟨12728614890897831966931331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8485743260598554644620887 12728614890897831966931331)
                  ·
                    refine ⟨19092922336346747950396997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12728614890897831966931331 19092922336346747950396997)
                    ·
                      refine ⟨3579922938065015240699437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19092922336346747950396997 3579922938065015240699437)
                      ·
                        rfl

theorem cell23_6971875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_6971875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971875 prefixEnd_6971875 := by exact prefixLift 6971875
  have htrace : WordTrace (prefixWord ++ tailWord_6971875) baseStart_6971875 baseEnd_6971875 := by
    simpa [prefixWord, tailWord_6971875, baseEnd_6971875] using wordTrace_append hprefix tailTrace_6971875
  have hstable : (prefixWord ++ tailWord_6971875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971875).length < 2 ^ (prefixWord ++ tailWord_6971875).sum := by decide
  have hdescent : baseEnd_6971875 < baseStart_6971875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971897 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 1, 5, 4]
def baseStart_6971897 : Nat := 118140960795 + 6971897 * 2 ^ 59
def prefixEnd_6971897 : Nat := 4983230072969 + 3 ^ 40 * 6971897 * 2
def baseEnd_6971897 : Nat := 3579934234639414154624335

theorem tailTrace_6971897 : CollatzResearch.WordTrace tailWord_6971897 prefixEnd_6971897 3579934234639414154624335 := by
  unfold tailWord_6971897
  simp only [CollatzResearch.WordTrace]
  refine ⟨254285974023015349055825945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169523982682010232703883963 254285974023015349055825945)
  ·
    refine ⟨190714480517261511791869459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254285974023015349055825945 190714480517261511791869459)
    ·
      refine ⟨286071720775892267687804189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190714480517261511791869459 286071720775892267687804189)
      ·
        refine ⟨107276895290959600382926571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286071720775892267687804189 107276895290959600382926571)
        ·
          refine ⟨160915342936439400574389857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107276895290959600382926571 160915342936439400574389857)
          ·
            refine ⟨120686507202329550430792393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160915342936439400574389857 120686507202329550430792393)
            ·
              refine ⟨90514880401747162823094295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120686507202329550430792393 90514880401747162823094295)
              ·
                refine ⟨135772320602620744234641443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90514880401747162823094295 135772320602620744234641443)
                ·
                  refine ⟨203658480903931116351962165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135772320602620744234641443 203658480903931116351962165)
                  ·
                    refine ⟨19092982584743542157996453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 203658480903931116351962165 19092982584743542157996453)
                    ·
                      refine ⟨3579934234639414154624335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19092982584743542157996453 3579934234639414154624335)
                      ·
                        rfl

theorem cell23_6971897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_6971897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971897 prefixEnd_6971897 := by exact prefixLift 6971897
  have htrace : WordTrace (prefixWord ++ tailWord_6971897) baseStart_6971897 baseEnd_6971897 := by
    simpa [prefixWord, tailWord_6971897, baseEnd_6971897] using wordTrace_append hprefix tailTrace_6971897
  have hstable : (prefixWord ++ tailWord_6971897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971897).length < 2 ^ (prefixWord ++ tailWord_6971897).sum := by decide
  have hdescent : baseEnd_6971897 < baseStart_6971897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971907 : List Nat := [1, 1, 1, 3, 2, 1, 3, 3, 2, 6]
def baseStart_6971907 : Nat := 118140960795 + 6971907 * 2 ^ 59
def prefixEnd_6971907 : Nat := 4983230072969 + 3 ^ 40 * 6971907 * 2
def baseEnd_6971907 : Nat := 1193313123148653038499763

theorem tailTrace_6971907 : CollatzResearch.WordTrace tailWord_6971907 prefixEnd_6971907 1193313123148653038499763 := by
  unfold tailWord_6971907
  simp only [CollatzResearch.WordTrace]
  refine ⟨254286338752979120763689975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169524225835319413842459983 254286338752979120763689975)
  ·
    refine ⟨381429508129468681145534963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254286338752979120763689975 381429508129468681145534963)
    ·
      refine ⟨572144262194203021718302445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381429508129468681145534963 572144262194203021718302445)
      ·
        refine ⟨214554098322826133144363417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 572144262194203021718302445 214554098322826133144363417)
        ·
          refine ⟨160915573742119599858272563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214554098322826133144363417 160915573742119599858272563)
          ·
            refine ⟨241373360613179399787408845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160915573742119599858272563 241373360613179399787408845)
            ·
              refine ⟨90515010229942274920278317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241373360613179399787408845 90515010229942274920278317)
              ·
                refine ⟨33943128836228353095104369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90515010229942274920278317 33943128836228353095104369)
                ·
                  refine ⟨25457346627171264821328277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33943128836228353095104369 25457346627171264821328277)
                  ·
                    refine ⟨1193313123148653038499763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25457346627171264821328277 1193313123148653038499763)
                    ·
                      rfl

theorem cell23_6971907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 6].length) (baseStart_6971907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971907 prefixEnd_6971907 := by exact prefixLift 6971907
  have htrace : WordTrace (prefixWord ++ tailWord_6971907) baseStart_6971907 baseEnd_6971907 := by
    simpa [prefixWord, tailWord_6971907, baseEnd_6971907] using wordTrace_append hprefix tailTrace_6971907
  have hstable : (prefixWord ++ tailWord_6971907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971907).length < 2 ^ (prefixWord ++ tailWord_6971907).sum := by decide
  have hdescent : baseEnd_6971907 < baseStart_6971907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971908 : List Nat := [2, 3, 2, 3, 1, 3, 1, 1, 1, 3, 3]
def baseStart_6971908 : Nat := 118140960795 + 6971908 * 2 ^ 59
def prefixEnd_6971908 : Nat := 4983230072969 + 3 ^ 40 * 6971908 * 2
def baseEnd_6971908 : Nat := 3579939882926613611586785

theorem tailTrace_6971908 : CollatzResearch.WordTrace tailWord_6971908 prefixEnd_6971908 3579939882926613611586785 := by
  unfold tailWord_6971908
  simp only [CollatzResearch.WordTrace]
  refine ⟨127143187612987748967238189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169524250150650331956317585 127143187612987748967238189)
  ·
    refine ⟨47678695354870405862714321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127143187612987748967238189 47678695354870405862714321)
    ·
      refine ⟨35759021516152804397035741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47678695354870405862714321 35759021516152804397035741)
      ·
        refine ⟨13409633068557301648888403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35759021516152804397035741 13409633068557301648888403)
        ·
          refine ⟨20114449602835952473332605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13409633068557301648888403 20114449602835952473332605)
          ·
            refine ⟨7542918601063482177499727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20114449602835952473332605 7542918601063482177499727)
            ·
              refine ⟨11314377901595223266249591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7542918601063482177499727 11314377901595223266249591)
              ·
                refine ⟨16971566852392834899374387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11314377901595223266249591 16971566852392834899374387)
                ·
                  refine ⟨25457350278589252349061581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16971566852392834899374387 25457350278589252349061581)
                  ·
                    refine ⟨9546506354470969630898093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25457350278589252349061581 9546506354470969630898093)
                    ·
                      refine ⟨3579939882926613611586785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9546506354470969630898093 3579939882926613611586785)
                      ·
                        rfl

theorem cell23_6971908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_6971908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971908 prefixEnd_6971908 := by exact prefixLift 6971908
  have htrace : WordTrace (prefixWord ++ tailWord_6971908) baseStart_6971908 baseEnd_6971908 := by
    simpa [prefixWord, tailWord_6971908, baseEnd_6971908] using wordTrace_append hprefix tailTrace_6971908
  have hstable : (prefixWord ++ tailWord_6971908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971908).length < 2 ^ (prefixWord ++ tailWord_6971908).sum := by decide
  have hdescent : baseEnd_6971908 < baseStart_6971908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971918 : List Nat := [4, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2]
def baseStart_6971918 : Nat := 118140960795 + 6971918 * 2 ^ 59
def prefixEnd_6971918 : Nat := 4983230072969 + 3 ^ 40 * 6971918 * 2
def baseEnd_6971918 : Nat := 3579945017733158572461739

theorem tailTrace_6971918 : CollatzResearch.WordTrace tailWord_6971918 prefixEnd_6971918 3579945017733158572461739 := by
  unfold tailWord_6971918
  simp only [CollatzResearch.WordTrace]
  refine ⟨31785842494492408705292551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169524493303959513094893605 31785842494492408705292551)
  ·
    refine ⟨47678763741738613057938827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31785842494492408705292551 47678763741738613057938827)
    ·
      refine ⟨71518145612607919586908241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47678763741738613057938827 71518145612607919586908241)
      ·
        refine ⟨53638609209455939690181181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71518145612607919586908241 53638609209455939690181181)
        ·
          refine ⟨20114478453545977383817943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53638609209455939690181181 20114478453545977383817943)
          ·
            refine ⟨30171717680318966075726915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20114478453545977383817943 30171717680318966075726915)
            ·
              refine ⟨45257576520478449113590373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30171717680318966075726915 45257576520478449113590373)
              ·
                refine ⟨8485795597589709208798195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45257576520478449113590373 8485795597589709208798195)
                ·
                  refine ⟨12728693396384563813197293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8485795597589709208798195 12728693396384563813197293)
                  ·
                    refine ⟨4773260023644211429948985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12728693396384563813197293 4773260023644211429948985)
                    ·
                      refine ⟨3579945017733158572461739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4773260023644211429948985 3579945017733158572461739)
                      ·
                        rfl

theorem cell23_6971918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_6971918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971918 prefixEnd_6971918 := by exact prefixLift 6971918
  have htrace : WordTrace (prefixWord ++ tailWord_6971918) baseStart_6971918 baseEnd_6971918 := by
    simpa [prefixWord, tailWord_6971918, baseEnd_6971918] using wordTrace_append hprefix tailTrace_6971918
  have hstable : (prefixWord ++ tailWord_6971918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971918).length < 2 ^ (prefixWord ++ tailWord_6971918).sum := by decide
  have hdescent : baseEnd_6971918 < baseStart_6971918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971954 : List Nat := [3, 2, 1, 1, 2, 1, 5, 1, 7]
def baseStart_6971954 : Nat := 118140960795 + 6971954 * 2 ^ 59
def prefixEnd_6971954 : Nat := 4983230072969 + 3 ^ 40 * 6971954 * 2
def baseEnd_6971954 : Nat := 397773722559635603512397

theorem tailTrace_6971954 : CollatzResearch.WordTrace tailWord_6971954 prefixEnd_6971954 397773722559635603512397 := by
  unfold tailWord_6971954
  simp only [CollatzResearch.WordTrace]
  refine ⟨63572013245952211947662729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169525368655872565193767277 63572013245952211947662729)
  ·
    refine ⟨47679009934464158960747047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63572013245952211947662729 47679009934464158960747047)
    ·
      refine ⟨71518514901696238441120571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47679009934464158960747047 71518514901696238441120571)
      ·
        refine ⟨107277772352544357661680857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71518514901696238441120571 107277772352544357661680857)
        ·
          refine ⟨80458329264408268246260643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107277772352544357661680857 80458329264408268246260643)
          ·
            refine ⟨120687493896612402369390965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80458329264408268246260643 120687493896612402369390965)
            ·
              refine ⟨11314452552807412722130403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120687493896612402369390965 11314452552807412722130403)
              ·
                refine ⟨16971678829211119083195605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11314452552807412722130403 16971678829211119083195605)
                ·
                  refine ⟨397773722559635603512397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16971678829211119083195605 397773722559635603512397)
                  ·
                    rfl

theorem cell23_6971954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 7].length) (baseStart_6971954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971954 prefixEnd_6971954 := by exact prefixLift 6971954
  have htrace : WordTrace (prefixWord ++ tailWord_6971954) baseStart_6971954 baseEnd_6971954 := by
    simpa [prefixWord, tailWord_6971954, baseEnd_6971954] using wordTrace_append hprefix tailTrace_6971954
  have hstable : (prefixWord ++ tailWord_6971954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971954).length < 2 ^ (prefixWord ++ tailWord_6971954).sum := by decide
  have hdescent : baseEnd_6971954 < baseStart_6971954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6971965 : List Nat := [1, 4, 1, 3, 2, 2, 1, 3, 2, 2, 2]
def baseStart_6971965 : Nat := 118140960795 + 6971965 * 2 ^ 59
def prefixEnd_6971965 : Nat := 4983230072969 + 3 ^ 40 * 6971965 * 2
def baseEnd_6971965 : Nat := 3579969151323919888574023

theorem tailTrace_6971965 : CollatzResearch.WordTrace tailWord_6971965 prefixEnd_6971965 3579969151323919888574023 := by
  unfold tailWord_6971965
  simp only [CollatzResearch.WordTrace]
  refine ⟨254288454186768996669301349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169525636124512664446200899 254288454186768996669301349)
  ·
    refine ⟨47679085160019186875494003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254288454186768996669301349 47679085160019186875494003)
    ·
      refine ⟨71518627740028780313241005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47679085160019186875494003 71518627740028780313241005)
      ·
        refine ⟨26819485402510792617465377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71518627740028780313241005 26819485402510792617465377)
        ·
          refine ⟨20114614051883094463099033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26819485402510792617465377 20114614051883094463099033)
          ·
            refine ⟨15085960538912320847324275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20114614051883094463099033 15085960538912320847324275)
            ·
              refine ⟨22628940808368481270986413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15085960538912320847324275 22628940808368481270986413)
              ·
                refine ⟨8485852803138180476619905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22628940808368481270986413 8485852803138180476619905)
                ·
                  refine ⟨6364389602353635357464929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8485852803138180476619905 6364389602353635357464929)
                  ·
                    refine ⟨4773292201765226518098697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6364389602353635357464929 4773292201765226518098697)
                    ·
                      refine ⟨3579969151323919888574023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4773292201765226518098697 3579969151323919888574023)
                      ·
                        rfl

theorem cell23_6971965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_6971965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6971965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6971965 prefixEnd_6971965 := by exact prefixLift 6971965
  have htrace : WordTrace (prefixWord ++ tailWord_6971965) baseStart_6971965 baseEnd_6971965 := by
    simpa [prefixWord, tailWord_6971965, baseEnd_6971965] using wordTrace_append hprefix tailTrace_6971965
  have hstable : (prefixWord ++ tailWord_6971965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6971965).length < 2 ^ (prefixWord ++ tailWord_6971965).sum := by decide
  have hdescent : baseEnd_6971965 < baseStart_6971965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6971965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972005 : List Nat := [1, 3, 1, 3, 4, 2, 2, 2, 5]
def baseStart_6972005 : Nat := 118140960795 + 6972005 * 2 ^ 59
def prefixEnd_6972005 : Nat := 4983230072969 + 3 ^ 40 * 6972005 * 2
def baseEnd_6972005 : Nat := 397776632283344414674871

theorem tailTrace_6972005 : CollatzResearch.WordTrace tailWord_6972005 prefixEnd_6972005 397776632283344414674871 := by
  unfold tailWord_6972005
  simp only [CollatzResearch.WordTrace]
  refine ⟨254289913106624083500757469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169526608737749389000504979 254289913106624083500757469)
  ·
    refine ⟨95358717414984031312784051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254289913106624083500757469 95358717414984031312784051)
    ·
      refine ⟨143038076122476046969176077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95358717414984031312784051 143038076122476046969176077)
      ·
        refine ⟨53639278545928517613441029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143038076122476046969176077 53639278545928517613441029)
        ·
          refine ⟨10057364727361597052520193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53639278545928517613441029 10057364727361597052520193)
          ·
            refine ⟨7543023545521197789390145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10057364727361597052520193 7543023545521197789390145)
            ·
              refine ⟨5657267659140898342042609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7543023545521197789390145 5657267659140898342042609)
              ·
                refine ⟨4242950744355673756531957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5657267659140898342042609 4242950744355673756531957)
                ·
                  refine ⟨397776632283344414674871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4242950744355673756531957 397776632283344414674871)
                  ·
                    rfl

theorem cell23_6972005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 2, 5].length) (baseStart_6972005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972005 prefixEnd_6972005 := by exact prefixLift 6972005
  have htrace : WordTrace (prefixWord ++ tailWord_6972005) baseStart_6972005 baseEnd_6972005 := by
    simpa [prefixWord, tailWord_6972005, baseEnd_6972005] using wordTrace_append hprefix tailTrace_6972005
  have hstable : (prefixWord ++ tailWord_6972005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972005).length < 2 ^ (prefixWord ++ tailWord_6972005).sum := by decide
  have hdescent : baseEnd_6972005 < baseStart_6972005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972024 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 3, 4, 3]
def baseStart_6972024 : Nat := 118140960795 + 6972024 * 2 ^ 59
def prefixEnd_6972024 : Nat := 4983230072969 + 3 ^ 40 * 6972024 * 2
def baseEnd_6972024 : Nat := 3579999446682535157736251

theorem tailTrace_6972024 : CollatzResearch.WordTrace tailWord_6972024 prefixEnd_6972024 3579999446682535157736251 := by
  unfold tailWord_6972024
  simp only [CollatzResearch.WordTrace]
  refine ⟨127145303046777624872849563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169527070729036833163799417 127145303046777624872849563)
  ·
    refine ⟨190717954570166437309274345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127145303046777624872849563 190717954570166437309274345)
    ·
      refine ⟨143038465927624827981955759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190717954570166437309274345 143038465927624827981955759)
      ·
        refine ⟨214557698891437241972933639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143038465927624827981955759 214557698891437241972933639)
        ·
          refine ⟨321836548337155862959400459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214557698891437241972933639 321836548337155862959400459)
          ·
            refine ⟨482754822505733794439100689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321836548337155862959400459 482754822505733794439100689)
            ·
              refine ⟨362066116879300345829325517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 482754822505733794439100689 362066116879300345829325517)
              ·
                refine ⟨135774793829737629685997069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 362066116879300345829325517 135774793829737629685997069)
                ·
                  refine ⟨50915547686151611132248901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135774793829737629685997069 50915547686151611132248901)
                  ·
                    refine ⟨9546665191153427087296669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50915547686151611132248901 9546665191153427087296669)
                    ·
                      refine ⟨3579999446682535157736251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9546665191153427087296669 3579999446682535157736251)
                      ·
                        rfl

theorem cell23_6972024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 3, 4, 3].length) (baseStart_6972024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972024 prefixEnd_6972024 := by exact prefixLift 6972024
  have htrace : WordTrace (prefixWord ++ tailWord_6972024) baseStart_6972024 baseEnd_6972024 := by
    simpa [prefixWord, tailWord_6972024, baseEnd_6972024] using wordTrace_append hprefix tailTrace_6972024
  have hstable : (prefixWord ++ tailWord_6972024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972024).length < 2 ^ (prefixWord ++ tailWord_6972024).sum := by decide
  have hdescent : baseEnd_6972024 < baseStart_6972024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972061 : List Nat := [1, 4, 2, 1, 1, 1, 5, 2, 6]
def baseStart_6972061 : Nat := 118140960795 + 6972061 * 2 ^ 59
def prefixEnd_6972061 : Nat := 4983230072969 + 3 ^ 40 * 6972061 * 2
def baseEnd_6972061 : Nat := 397779827274083501441509

theorem tailTrace_6972061 : CollatzResearch.WordTrace tailWord_6972061 prefixEnd_6972061 397779827274083501441509 := by
  unfold tailWord_6972061
  simp only [CollatzResearch.WordTrace]
  refine ⟨254291955594421205064796037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169527970396280803376530691 254291955594421205064796037)
  ·
    refine ⟨47679741673953975949649257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254291955594421205064796037 47679741673953975949649257)
    ·
      refine ⟨35759806255465481962236943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47679741673953975949649257 35759806255465481962236943)
      ·
        refine ⟨53639709383198222943355415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35759806255465481962236943 53639709383198222943355415)
        ·
          refine ⟨80459564074797334415033123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53639709383198222943355415 80459564074797334415033123)
          ·
            refine ⟨120689346112196001622549685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80459564074797334415033123 120689346112196001622549685)
            ·
              refine ⟨11314626198018375152114033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120689346112196001622549685 11314626198018375152114033)
              ·
                refine ⟨8485969648513781364085525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11314626198018375152114033 8485969648513781364085525)
                ·
                  refine ⟨397779827274083501441509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8485969648513781364085525 397779827274083501441509)
                  ·
                    rfl

theorem cell23_6972061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 6].length) (baseStart_6972061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972061 prefixEnd_6972061 := by exact prefixLift 6972061
  have htrace : WordTrace (prefixWord ++ tailWord_6972061) baseStart_6972061 baseEnd_6972061 := by
    simpa [prefixWord, tailWord_6972061, baseEnd_6972061] using wordTrace_append hprefix tailTrace_6972061
  have hstable : (prefixWord ++ tailWord_6972061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972061).length < 2 ^ (prefixWord ++ tailWord_6972061).sum := by decide
  have hdescent : baseEnd_6972061 < baseStart_6972061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972108 : List Nat := [2, 2, 1, 5, 1, 1, 2, 3, 1, 5]
def baseStart_6972108 : Nat := 118140960795 + 6972108 * 2 ^ 59
def prefixEnd_6972108 : Nat := 4983230072969 + 3 ^ 40 * 6972108 * 2
def baseEnd_6972108 : Nat := 1193347526352504276361955

theorem tailTrace_6972108 : CollatzResearch.WordTrace tailWord_6972108 prefixEnd_6972108 1193347526352504276361955 := by
  unfold tailWord_6972108
  simp only [CollatzResearch.WordTrace]
  refine ⟨127146834912625466045878489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169529113216833954727837985 127146834912625466045878489)
  ·
    refine ⟨95360126184469099534408867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127146834912625466045878489 95360126184469099534408867)
    ·
      refine ⟨143040189276703649301613301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95360126184469099534408867 143040189276703649301613301)
      ·
        refine ⟨13410017744690967122026247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143040189276703649301613301 13410017744690967122026247)
        ·
          refine ⟨20115026617036450683039371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13410017744690967122026247 20115026617036450683039371)
          ·
            refine ⟨30172539925554676024559057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20115026617036450683039371 30172539925554676024559057)
            ·
              refine ⟨22629404944166007018419293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30172539925554676024559057 22629404944166007018419293)
              ·
                refine ⟨8486026854062252631907235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22629404944166007018419293 8486026854062252631907235)
                ·
                  refine ⟨12729040281093378947860853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8486026854062252631907235 12729040281093378947860853)
                  ·
                    refine ⟨1193347526352504276361955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12729040281093378947860853 1193347526352504276361955)
                    ·
                      rfl

theorem cell23_6972108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 1, 5].length) (baseStart_6972108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972108 prefixEnd_6972108 := by exact prefixLift 6972108
  have htrace : WordTrace (prefixWord ++ tailWord_6972108) baseStart_6972108 baseEnd_6972108 := by
    simpa [prefixWord, tailWord_6972108, baseEnd_6972108] using wordTrace_append hprefix tailTrace_6972108
  have hstable : (prefixWord ++ tailWord_6972108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972108).length < 2 ^ (prefixWord ++ tailWord_6972108).sum := by decide
  have hdescent : baseEnd_6972108 < baseStart_6972108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972121 : List Nat := [1, 2, 1, 2, 3, 2, 1, 3, 4, 4]
def baseStart_6972121 : Nat := 118140960795 + 6972121 * 2 ^ 59
def prefixEnd_6972121 : Nat := 4983230072969 + 3 ^ 40 * 6972121 * 2
def baseEnd_6972121 : Nat := 1193349751435340426074435

theorem tailTrace_6972121 : CollatzResearch.WordTrace tailWord_6972121 prefixEnd_6972121 1193349751435340426074435 := by
  unfold tailWord_6972121
  simp only [CollatzResearch.WordTrace]
  refine ⟨254294143974203835311980217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169529429316135890207986811 254294143974203835311980217)
  ·
    refine ⟨190720607980652876483985163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254294143974203835311980217 190720607980652876483985163)
    ·
      refine ⟨286080911970979314725977745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190720607980652876483985163 286080911970979314725977745)
      ·
        refine ⟨214560683978234486044483309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286080911970979314725977745 214560683978234486044483309)
        ·
          refine ⟨80460256491837932266681241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214560683978234486044483309 80460256491837932266681241)
          ·
            refine ⟨60345192368878449200010931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80460256491837932266681241 60345192368878449200010931)
            ·
              refine ⟨90517788553317673800016397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60345192368878449200010931 90517788553317673800016397)
              ·
                refine ⟨33944170707494127675006149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90517788553317673800016397 33944170707494127675006149)
                ·
                  refine ⟨6364532007655148939063653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33944170707494127675006149 6364532007655148939063653)
                  ·
                    refine ⟨1193349751435340426074435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6364532007655148939063653 1193349751435340426074435)
                    ·
                      rfl

theorem cell23_6972121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 4, 4].length) (baseStart_6972121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972121 prefixEnd_6972121 := by exact prefixLift 6972121
  have htrace : WordTrace (prefixWord ++ tailWord_6972121) baseStart_6972121 baseEnd_6972121 := by
    simpa [prefixWord, tailWord_6972121, baseEnd_6972121] using wordTrace_append hprefix tailTrace_6972121
  have hstable : (prefixWord ++ tailWord_6972121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972121).length < 2 ^ (prefixWord ++ tailWord_6972121).sum := by decide
  have hdescent : baseEnd_6972121 < baseStart_6972121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972122 : List Nat := [3, 1, 1, 2, 2, 2, 5, 2, 1, 1, 3]
def baseStart_6972122 : Nat := 118140960795 + 6972122 * 2 ^ 59
def prefixEnd_6972122 : Nat := 4983230072969 + 3 ^ 40 * 6972122 * 2
def baseEnd_6972122 : Nat := 3580049767786675774310801

theorem tailTrace_6972122 : CollatzResearch.WordTrace tailWord_6972122 prefixEnd_6972122 3580049767786675774310801 := by
  unfold tailWord_6972122
  simp only [CollatzResearch.WordTrace]
  refine ⟨63573545111800053120691655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169529453631466808321844413 63573545111800053120691655)
  ·
    refine ⟨95360317667700079681037483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63573545111800053120691655 95360317667700079681037483)
    ·
      refine ⟨143040476501550119521556225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95360317667700079681037483 143040476501550119521556225)
      ·
        refine ⟨107280357376162589641167169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143040476501550119521556225 107280357376162589641167169)
        ·
          refine ⟨80460268032121942230875377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107280357376162589641167169 80460268032121942230875377)
          ·
            refine ⟨60345201024091456673156533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80460268032121942230875377 60345201024091456673156533)
            ·
              refine ⟨5657362596008574063108425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60345201024091456673156533 5657362596008574063108425)
              ·
                refine ⟨4243021947006430547331319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5657362596008574063108425 4243021947006430547331319)
                ·
                  refine ⟨6364532920509645820996979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4243021947006430547331319 6364532920509645820996979)
                  ·
                    refine ⟨9546799380764468731495469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6364532920509645820996979 9546799380764468731495469)
                    ·
                      refine ⟨3580049767786675774310801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9546799380764468731495469 3580049767786675774310801)
                      ·
                        rfl

theorem cell23_6972122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 2, 1, 1, 3].length) (baseStart_6972122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972122 prefixEnd_6972122 := by exact prefixLift 6972122
  have htrace : WordTrace (prefixWord ++ tailWord_6972122) baseStart_6972122 baseEnd_6972122 := by
    simpa [prefixWord, tailWord_6972122, baseEnd_6972122] using wordTrace_append hprefix tailTrace_6972122
  have hstable : (prefixWord ++ tailWord_6972122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972122).length < 2 ^ (prefixWord ++ tailWord_6972122).sum := by decide
  have hdescent : baseEnd_6972122 < baseStart_6972122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972141 : List Nat := [1, 5, 1, 2, 1, 1, 1, 3, 1, 1, 6]
def baseStart_6972141 : Nat := 118140960795 + 6972141 * 2 ^ 59
def prefixEnd_6972141 : Nat := 4983230072969 + 3 ^ 40 * 6972141 * 2
def baseEnd_6972141 : Nat := 3580059523919111199973213

theorem tailTrace_6972141 : CollatzResearch.WordTrace tailWord_6972141 prefixEnd_6972141 3580059523919111199973213 := by
  unfold tailWord_6972141
  simp only [CollatzResearch.WordTrace]
  refine ⟨254294873434131378727708277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169529915622754252485138851 254294873434131378727708277)
  ·
    refine ⟨23840144384449816755722651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 254294873434131378727708277 23840144384449816755722651)
    ·
      refine ⟨35760216576674725133583977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23840144384449816755722651 35760216576674725133583977)
      ·
        refine ⟨26820162432506043850187983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35760216576674725133583977 26820162432506043850187983)
        ·
          refine ⟨40230243648759065775281975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26820162432506043850187983 40230243648759065775281975)
          ·
            refine ⟨60345365473138598662922963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40230243648759065775281975 60345365473138598662922963)
            ·
              refine ⟨90518048209707897994384445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60345365473138598662922963 90518048209707897994384445)
              ·
                refine ⟨33944268078640461747894167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90518048209707897994384445 33944268078640461747894167)
                ·
                  refine ⟨50916402117960692621841251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33944268078640461747894167 50916402117960692621841251)
                  ·
                    refine ⟨76374603176941038932761877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50916402117960692621841251 76374603176941038932761877)
                    ·
                      refine ⟨3580059523919111199973213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76374603176941038932761877 3580059523919111199973213)
                      ·
                        rfl

theorem cell23_6972141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_6972141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972141 prefixEnd_6972141 := by exact prefixLift 6972141
  have htrace : WordTrace (prefixWord ++ tailWord_6972141) baseStart_6972141 baseEnd_6972141 := by
    simpa [prefixWord, tailWord_6972141, baseEnd_6972141] using wordTrace_append hprefix tailTrace_6972141
  have hstable : (prefixWord ++ tailWord_6972141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972141).length < 2 ^ (prefixWord ++ tailWord_6972141).sum := by decide
  have hdescent : baseEnd_6972141 < baseStart_6972141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972158 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_6972158 : Nat := 118140960795 + 6972158 * 2 ^ 59
def prefixEnd_6972158 : Nat := 4983230072969 + 3 ^ 40 * 6972158 * 2
def baseEnd_6972158 : Nat := 3580068253090237633460635

theorem tailTrace_6972158 : CollatzResearch.WordTrace tailWord_6972158 prefixEnd_6972158 3580068253090237633460635 := by
  unfold tailWord_6972158
  simp only [CollatzResearch.WordTrace]
  refine ⟨31786936684383723828884641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169530328983379860420718085 31786936684383723828884641)
  ·
    refine ⟨23840202513287792871663481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31786936684383723828884641 23840202513287792871663481)
    ·
      refine ⟨17880151884965844653747611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23840202513287792871663481 17880151884965844653747611)
      ·
        refine ⟨26820227827448766980621417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17880151884965844653747611 26820227827448766980621417)
        ·
          refine ⟨20115170870586575235466063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26820227827448766980621417 20115170870586575235466063)
          ·
            refine ⟨30172756305879862853199095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20115170870586575235466063 30172756305879862853199095)
            ·
              refine ⟨45259134458819794279798643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30172756305879862853199095 45259134458819794279798643)
              ·
                refine ⟨67888701688229691419697965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45259134458819794279798643 67888701688229691419697965)
                ·
                  refine ⟨25458263133086134282386737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67888701688229691419697965 25458263133086134282386737)
                  ·
                    refine ⟨19093697349814600711790053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25458263133086134282386737 19093697349814600711790053)
                    ·
                      refine ⟨3580068253090237633460635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19093697349814600711790053 3580068253090237633460635)
                      ·
                        rfl

theorem cell23_6972158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_6972158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972158 prefixEnd_6972158 := by exact prefixLift 6972158
  have htrace : WordTrace (prefixWord ++ tailWord_6972158) baseStart_6972158 baseEnd_6972158 := by
    simpa [prefixWord, tailWord_6972158, baseEnd_6972158] using wordTrace_append hprefix tailTrace_6972158
  have hstable : (prefixWord ++ tailWord_6972158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972158).length < 2 ^ (prefixWord ++ tailWord_6972158).sum := by decide
  have hdescent : baseEnd_6972158 < baseStart_6972158 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972162 : List Nat := [3, 4, 1, 1, 1, 3, 3, 1, 1, 1, 4]
def baseStart_6972162 : Nat := 118140960795 + 6972162 * 2 ^ 59
def prefixEnd_6972162 : Nat := 4983230072969 + 3 ^ 40 * 6972162 * 2
def baseEnd_6972162 : Nat := 3580070307012855617810617

theorem tailTrace_6972162 : CollatzResearch.WordTrace tailWord_6972162 prefixEnd_6972162 3580070307012855617810617 := by
  unfold tailWord_6972162
  simp only [CollatzResearch.WordTrace]
  refine ⟨63573909841763824828555685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169530426244703532876148493 63573909841763824828555685)
  ·
    refine ⟨11920108095330717155354191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63573909841763824828555685 11920108095330717155354191)
    ·
      refine ⟨17880162142996075733031287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11920108095330717155354191 17880162142996075733031287)
      ·
        refine ⟨26820243214494113599546931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17880162142996075733031287 26820243214494113599546931)
        ·
          refine ⟨40230364821741170399320397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26820243214494113599546931 40230364821741170399320397)
          ·
            refine ⟨15086386808152938899745149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40230364821741170399320397 15086386808152938899745149)
            ·
              refine ⟨5657395053057352087404431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15086386808152938899745149 5657395053057352087404431)
              ·
                refine ⟨8486092579586028131106647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5657395053057352087404431 8486092579586028131106647)
                ·
                  refine ⟨12729138869379042196659971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8486092579586028131106647 12729138869379042196659971)
                  ·
                    refine ⟨19093708304068563294989957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12729138869379042196659971 19093708304068563294989957)
                    ·
                      refine ⟨3580070307012855617810617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19093708304068563294989957 3580070307012855617810617)
                      ·
                        rfl

theorem cell23_6972162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_6972162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972162 prefixEnd_6972162 := by exact prefixLift 6972162
  have htrace : WordTrace (prefixWord ++ tailWord_6972162) baseStart_6972162 baseEnd_6972162 := by
    simpa [prefixWord, tailWord_6972162, baseEnd_6972162] using wordTrace_append hprefix tailTrace_6972162
  have hstable : (prefixWord ++ tailWord_6972162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972162).length < 2 ^ (prefixWord ++ tailWord_6972162).sum := by decide
  have hdescent : baseEnd_6972162 < baseStart_6972162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972251 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 7, 5, 3]
def baseStart_6972251 : Nat := 118140960795 + 6972251 * 2 ^ 59
def prefixEnd_6972251 : Nat := 4983230072969 + 3 ^ 40 * 6972251 * 2
def baseEnd_6972251 : Nat := 3580116006791105769597707

theorem tailTrace_6972251 : CollatzResearch.WordTrace tailWord_6972251 prefixEnd_6972251 3580116006791105769597707 := by
  unfold tailWord_6972251
  simp only [CollatzResearch.WordTrace]
  refine ⟨254298885463732867514212607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169532590309155245009475071 254298885463732867514212607)
  ·
    refine ⟨381448328195599301271318911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254298885463732867514212607 381448328195599301271318911)
    ·
      refine ⟨572172492293398951906978367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381448328195599301271318911 572172492293398951906978367)
      ·
        refine ⟨858258738440098427860467551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572172492293398951906978367 858258738440098427860467551)
        ·
          refine ⟨1287388107660147641790701327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 858258738440098427860467551 1287388107660147641790701327)
          ·
            refine ⟨1931082161490221462686051991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1287388107660147641790701327 1931082161490221462686051991)
            ·
              refine ⟨2896623242235332194029077987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1931082161490221462686051991 2896623242235332194029077987)
              ·
                refine ⟨4344934863352998291043616981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2896623242235332194029077987 4344934863352998291043616981)
                ·
                  refine ⟨101834410859835897446334773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4344934863352998291043616981 101834410859835897446334773)
                  ·
                    refine ⟨9546976018109615385593885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101834410859835897446334773 9546976018109615385593885)
                    ·
                      refine ⟨3580116006791105769597707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9546976018109615385593885 3580116006791105769597707)
                      ·
                        rfl

theorem cell23_6972251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 5, 3].length) (baseStart_6972251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972251 prefixEnd_6972251 := by exact prefixLift 6972251
  have htrace : WordTrace (prefixWord ++ tailWord_6972251) baseStart_6972251 baseEnd_6972251 := by
    simpa [prefixWord, tailWord_6972251, baseEnd_6972251] using wordTrace_append hprefix tailTrace_6972251
  have hstable : (prefixWord ++ tailWord_6972251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972251).length < 2 ^ (prefixWord ++ tailWord_6972251).sum := by decide
  have hdescent : baseEnd_6972251 < baseStart_6972251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972252 : List Nat := [2, 2, 4, 2, 1, 1, 3, 1, 1, 4, 2]
def baseStart_6972252 : Nat := 118140960795 + 6972252 * 2 ^ 59
def prefixEnd_6972252 : Nat := 4983230072969 + 3 ^ 40 * 6972252 * 2
def baseEnd_6972252 : Nat := 3580116520271760265685203

theorem tailTrace_6972252 : CollatzResearch.WordTrace tailWord_6972252 prefixEnd_6972252 3580116520271760265685203 := by
  unfold tailWord_6972252
  simp only [CollatzResearch.WordTrace]
  refine ⟨127149460968364622342499505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169532614624486163123332673 127149460968364622342499505)
  ·
    refine ⟨95362095726273466756874629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127149460968364622342499505 95362095726273466756874629)
    ·
      refine ⟨17880392948676275016913993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95362095726273466756874629 17880392948676275016913993)
      ·
        refine ⟨13410294711507206262685495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17880392948676275016913993 13410294711507206262685495)
        ·
          refine ⟨20115442067260809394028243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13410294711507206262685495 20115442067260809394028243)
          ·
            refine ⟨30173163100891214091042365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20115442067260809394028243 30173163100891214091042365)
            ·
              refine ⟨11314936162834205284140887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30173163100891214091042365 11314936162834205284140887)
              ·
                refine ⟨16972404244251307926211331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11314936162834205284140887 16972404244251307926211331)
                ·
                  refine ⟨25458606366376961889316997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16972404244251307926211331 25458606366376961889316997)
                  ·
                    refine ⟨4773488693695680354246937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25458606366376961889316997 4773488693695680354246937)
                    ·
                      refine ⟨3580116520271760265685203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4773488693695680354246937 3580116520271760265685203)
                      ·
                        rfl

theorem cell23_6972252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_6972252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972252 prefixEnd_6972252 := by exact prefixLift 6972252
  have htrace : WordTrace (prefixWord ++ tailWord_6972252) baseStart_6972252 baseEnd_6972252 := by
    simpa [prefixWord, tailWord_6972252, baseEnd_6972252] using wordTrace_append hprefix tailTrace_6972252
  have hstable : (prefixWord ++ tailWord_6972252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972252).length < 2 ^ (prefixWord ++ tailWord_6972252).sum := by decide
  have hdescent : baseEnd_6972252 < baseStart_6972252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972271 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 6, 5]
def baseStart_6972271 : Nat := 118140960795 + 6972271 * 2 ^ 59
def prefixEnd_6972271 : Nat := 4983230072969 + 3 ^ 40 * 6972271 * 2
def baseEnd_6972271 : Nat := 1193375425468065230449205

theorem tailTrace_6972271 : CollatzResearch.WordTrace tailWord_6972271 prefixEnd_6972271 1193375425468065230449205 := by
  unfold tailWord_6972271
  simp only [CollatzResearch.WordTrace]
  refine ⟨254299614923660410929940667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169533076615773607286627111 254299614923660410929940667)
  ·
    refine ⟨381449422385490616394911001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254299614923660410929940667 381449422385490616394911001)
    ·
      refine ⟨286087066789117962296183251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381449422385490616394911001 286087066789117962296183251)
      ·
        refine ⟨429130600183676943444274877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286087066789117962296183251 429130600183676943444274877)
        ·
          refine ⟨160923975068878853791603079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 429130600183676943444274877 160923975068878853791603079)
          ·
            refine ⟨241385962603318280687404619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160923975068878853791603079 241385962603318280687404619)
            ·
              refine ⟨362078943904977421031106929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241385962603318280687404619 362078943904977421031106929)
              ·
                refine ⟨271559207928733065773330197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 362078943904977421031106929 271559207928733065773330197)
                ·
                  refine ⟨12729337871659362458124853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 271559207928733065773330197 12729337871659362458124853)
                  ·
                    refine ⟨1193375425468065230449205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12729337871659362458124853 1193375425468065230449205)
                    ·
                      rfl

theorem cell23_6972271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 5].length) (baseStart_6972271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972271 prefixEnd_6972271 := by exact prefixLift 6972271
  have htrace : WordTrace (prefixWord ++ tailWord_6972271) baseStart_6972271 baseEnd_6972271 := by
    simpa [prefixWord, tailWord_6972271, baseEnd_6972271] using wordTrace_append hprefix tailTrace_6972271
  have hstable : (prefixWord ++ tailWord_6972271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972271).length < 2 ^ (prefixWord ++ tailWord_6972271).sum := by decide
  have hdescent : baseEnd_6972271 < baseStart_6972271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972298 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 1, 1, 7]
def baseStart_6972298 : Nat := 118140960795 + 6972298 * 2 ^ 59
def prefixEnd_6972298 : Nat := 4983230072969 + 3 ^ 40 * 6972298 * 2
def baseEnd_6972298 : Nat := 3580140140381867085709991

theorem tailTrace_6972298 : CollatzResearch.WordTrace tailWord_6972298 prefixEnd_6972298 3580140140381867085709991 := by
  unfold tailWord_6972298
  simp only [CollatzResearch.WordTrace]
  refine ⟨63575149923640648635293387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169533733129708396360782365 63575149923640648635293387)
  ·
    refine ⟨95362724885460972952940081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63575149923640648635293387 95362724885460972952940081)
    ·
      refine ⟨71522043664095729714705061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95362724885460972952940081 71522043664095729714705061)
      ·
        refine ⟨13410383187017949321507199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71522043664095729714705061 13410383187017949321507199)
        ·
          refine ⟨20115574780526923982260799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13410383187017949321507199 20115574780526923982260799)
          ·
            refine ⟨30173362170790385973391199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20115574780526923982260799 30173362170790385973391199)
            ·
              refine ⟨45260043256185578960086799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30173362170790385973391199 45260043256185578960086799)
              ·
                refine ⟨67890064884278368440130199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45260043256185578960086799 67890064884278368440130199)
                ·
                  refine ⟨101835097326417552660195299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67890064884278368440130199 101835097326417552660195299)
                  ·
                    refine ⟨152752645989626328990292949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101835097326417552660195299 152752645989626328990292949)
                    ·
                      refine ⟨3580140140381867085709991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152752645989626328990292949 3580140140381867085709991)
                      ·
                        rfl

theorem cell23_6972298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_6972298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972298 prefixEnd_6972298 := by exact prefixLift 6972298
  have htrace : WordTrace (prefixWord ++ tailWord_6972298) baseStart_6972298 baseEnd_6972298 := by
    simpa [prefixWord, tailWord_6972298, baseEnd_6972298] using wordTrace_append hprefix tailTrace_6972298
  have hstable : (prefixWord ++ tailWord_6972298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972298).length < 2 ^ (prefixWord ++ tailWord_6972298).sum := by decide
  have hdescent : baseEnd_6972298 < baseStart_6972298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972345 : List Nat := [1, 2, 1, 4, 2, 2, 2, 2, 2, 2, 3]
def baseStart_6972345 : Nat := 118140960795 + 6972345 * 2 ^ 59
def prefixEnd_6972345 : Nat := 4983230072969 + 3 ^ 40 * 6972345 * 2
def baseEnd_6972345 : Nat := 3580164273972628401822275

theorem tailTrace_6972345 : CollatzResearch.WordTrace tailWord_6972345 prefixEnd_6972345 3580164273972628401822275 := by
  unfold tailWord_6972345
  simp only [CollatzResearch.WordTrace]
  refine ⟨254302313925392321568134489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169534875950261547712089659 254302313925392321568134489)
  ·
    refine ⟨190726735444044241176100867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254302313925392321568134489 190726735444044241176100867)
    ·
      refine ⟨286090103166066361764151301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190726735444044241176100867 286090103166066361764151301)
      ·
        refine ⟨53641894343637442830778369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286090103166066361764151301 53641894343637442830778369)
        ·
          refine ⟨40231420757728082123083777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53641894343637442830778369 40231420757728082123083777)
          ·
            refine ⟨30173565568296061592312833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40231420757728082123083777 30173565568296061592312833)
            ·
              refine ⟨22630174176222046194234625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30173565568296061592312833 22630174176222046194234625)
              ·
                refine ⟨16972630632166534645675969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22630174176222046194234625 16972630632166534645675969)
                ·
                  refine ⟨12729472974124900984256977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16972630632166534645675969 12729472974124900984256977)
                  ·
                    refine ⟨9547104730593675738192733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12729472974124900984256977 9547104730593675738192733)
                    ·
                      refine ⟨3580164273972628401822275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9547104730593675738192733 3580164273972628401822275)
                      ·
                        rfl

theorem cell23_6972345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_6972345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972345 prefixEnd_6972345 := by exact prefixLift 6972345
  have htrace : WordTrace (prefixWord ++ tailWord_6972345) baseStart_6972345 baseEnd_6972345 := by
    simpa [prefixWord, tailWord_6972345, baseEnd_6972345] using wordTrace_append hprefix tailTrace_6972345
  have hstable : (prefixWord ++ tailWord_6972345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972345).length < 2 ^ (prefixWord ++ tailWord_6972345).sum := by decide
  have hdescent : baseEnd_6972345 < baseStart_6972345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972352 : List Nat := [2, 1, 1, 2, 3, 4, 1, 4, 1, 4]
def baseStart_6972352 : Nat := 118140960795 + 6972352 * 2 ^ 59
def prefixEnd_6972352 : Nat := 4983230072969 + 3 ^ 40 * 6972352 * 2
def baseEnd_6972352 : Nat := 1193389289445736624811581

theorem tailTrace_6972352 : CollatzResearch.WordTrace tailWord_6972352 prefixEnd_6972352 1193389289445736624811581 := by
  unfold tailWord_6972352
  simp only [CollatzResearch.WordTrace]
  refine ⟨127151284618183480881819655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169535046157577974509092873 127151284618183480881819655)
  ·
    refine ⟨190726926927275221322729483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127151284618183480881819655 190726926927275221322729483)
    ·
      refine ⟨286090390390912831984094225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190726926927275221322729483 286090390390912831984094225)
      ·
        refine ⟨214567792793184623988070669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286090390390912831984094225 214567792793184623988070669)
        ·
          refine ⟨80462922297444233995526501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214567792793184623988070669 80462922297444233995526501)
          ·
            refine ⟨15086797930770793874161219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80462922297444233995526501 15086797930770793874161219)
            ·
              refine ⟨22630196896156190811241829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15086797930770793874161219 22630196896156190811241829)
              ·
                refine ⟨4243161918029285777107843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22630196896156190811241829 4243161918029285777107843)
                ·
                  refine ⟨6364742877043928665661765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4243161918029285777107843 6364742877043928665661765)
                  ·
                    refine ⟨1193389289445736624811581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6364742877043928665661765 1193389289445736624811581)
                    ·
                      rfl

theorem cell23_6972352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 4, 1, 4].length) (baseStart_6972352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972352 prefixEnd_6972352 := by exact prefixLift 6972352
  have htrace : WordTrace (prefixWord ++ tailWord_6972352) baseStart_6972352 baseEnd_6972352 := by
    simpa [prefixWord, tailWord_6972352, baseEnd_6972352] using wordTrace_append hprefix tailTrace_6972352
  have hstable : (prefixWord ++ tailWord_6972352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972352).length < 2 ^ (prefixWord ++ tailWord_6972352).sum := by decide
  have hdescent : baseEnd_6972352 < baseStart_6972352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972361 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 1, 11]
def baseStart_6972361 : Nat := 118140960795 + 6972361 * 2 ^ 59
def prefixEnd_6972361 : Nat := 4983230072969 + 3 ^ 40 * 6972361 * 2
def baseEnd_6972361 : Nat := 1193390829887700113074067

theorem tailTrace_6972361 : CollatzResearch.WordTrace tailWord_6972361 prefixEnd_6972361 1193390829887700113074067 := by
  unfold tailWord_6972361
  simp only [CollatzResearch.WordTrace]
  refine ⟨254302897493334356300716937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169535264995556237533811291 254302897493334356300716937)
  ·
    refine ⟨190727173120000767225537703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254302897493334356300716937 190727173120000767225537703)
    ·
      refine ⟨286090759680001150838306555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190727173120000767225537703 286090759680001150838306555)
      ·
        refine ⟨429136139520001726257459833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286090759680001150838306555 429136139520001726257459833)
        ·
          refine ⟨321852104640001294693094875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429136139520001726257459833 321852104640001294693094875)
          ·
            refine ⟨482778156960001942039642313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321852104640001294693094875 482778156960001942039642313)
            ·
              refine ⟨362083617720001456529731735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 482778156960001942039642313 362083617720001456529731735)
              ·
                refine ⟨543125426580002184794597603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362083617720001456529731735 543125426580002184794597603)
                ·
                  refine ⟨814688139870003277191896405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 543125426580002184794597603 814688139870003277191896405)
                  ·
                    refine ⟨1193390829887700113074067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 814688139870003277191896405 1193390829887700113074067)
                    ·
                      rfl

theorem cell23_6972361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 11].length) (baseStart_6972361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972361 prefixEnd_6972361 := by exact prefixLift 6972361
  have htrace : WordTrace (prefixWord ++ tailWord_6972361) baseStart_6972361 baseEnd_6972361 := by
    simpa [prefixWord, tailWord_6972361, baseEnd_6972361] using wordTrace_append hprefix tailTrace_6972361
  have hstable : (prefixWord ++ tailWord_6972361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972361).length < 2 ^ (prefixWord ++ tailWord_6972361).sum := by decide
  have hdescent : baseEnd_6972361 < baseStart_6972361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972386 : List Nat := [3, 3, 3, 1, 1, 2, 2, 3, 1, 4]
def baseStart_6972386 : Nat := 118140960795 + 6972386 * 2 ^ 59
def prefixEnd_6972386 : Nat := 4983230072969 + 3 ^ 40 * 6972386 * 2
def baseEnd_6972386 : Nat := 1193395108893154247136529

theorem tailTrace_6972386 : CollatzResearch.WordTrace tailWord_6972386 prefixEnd_6972386 1193395108893154247136529 := by
  unfold tailWord_6972386
  simp only [CollatzResearch.WordTrace]
  refine ⟨63575952329560946392594253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169535872878829190380251341 63575952329560946392594253)
  ·
    refine ⟨23840982123585354897222845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63575952329560946392594253 23840982123585354897222845)
    ·
      refine ⟨8940368296344508086458567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23840982123585354897222845 8940368296344508086458567)
      ·
        refine ⟨13410552444516762129687851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8940368296344508086458567 13410552444516762129687851)
        ·
          refine ⟨20115828666775143194531777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13410552444516762129687851 20115828666775143194531777)
          ·
            refine ⟨15086871500081357395898833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20115828666775143194531777 15086871500081357395898833)
            ·
              refine ⟨11315153625061018046924125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15086871500081357395898833 11315153625061018046924125)
              ·
                refine ⟨4243182609397881767596547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11315153625061018046924125 4243182609397881767596547)
                ·
                  refine ⟨6364773914096822651394821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4243182609397881767596547 6364773914096822651394821)
                  ·
                    refine ⟨1193395108893154247136529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6364773914096822651394821 1193395108893154247136529)
                    ·
                      rfl

theorem cell23_6972386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_6972386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972386 prefixEnd_6972386 := by exact prefixLift 6972386
  have htrace : WordTrace (prefixWord ++ tailWord_6972386) baseStart_6972386 baseEnd_6972386 := by
    simpa [prefixWord, tailWord_6972386, baseEnd_6972386] using wordTrace_append hprefix tailTrace_6972386
  have hstable : (prefixWord ++ tailWord_6972386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972386).length < 2 ^ (prefixWord ++ tailWord_6972386).sum := by decide
  have hdescent : baseEnd_6972386 < baseStart_6972386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972425 : List Nat := [1, 2, 1, 1, 3, 1, 1, 7, 2, 4]
def baseStart_6972425 : Nat := 118140960795 + 6972425 * 2 ^ 59
def prefixEnd_6972425 : Nat := 4983230072969 + 3 ^ 40 * 6972425 * 2
def baseEnd_6972425 : Nat := 1193401784141662696273969

theorem tailTrace_6972425 : CollatzResearch.WordTrace tailWord_6972425 prefixEnd_6972425 1193401784141662696273969 := by
  unfold tailWord_6972425
  simp only [CollatzResearch.WordTrace]
  refine ⟨254305231765102495231046729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169536821176734996820697819 254305231765102495231046729)
  ·
    refine ⟨190728923823826871423285047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254305231765102495231046729 190728923823826871423285047)
    ·
      refine ⟨286093385735740307134927571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190728923823826871423285047 286093385735740307134927571)
      ·
        refine ⟨429140078603610460702391357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286093385735740307134927571 429140078603610460702391357)
        ·
          refine ⟨160927529476353922763396759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 429140078603610460702391357 160927529476353922763396759)
          ·
            refine ⟨241391294214530884145095139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160927529476353922763396759 241391294214530884145095139)
            ·
              refine ⟨362086941321796326217642709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241391294214530884145095139 362086941321796326217642709)
              ·
                refine ⟨8486412687229601395726001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 362086941321796326217642709 8486412687229601395726001)
                ·
                  refine ⟨6364809515422201046794501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8486412687229601395726001 6364809515422201046794501)
                  ·
                    refine ⟨1193401784141662696273969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6364809515422201046794501 1193401784141662696273969)
                    ·
                      rfl

theorem cell23_6972425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 2, 4].length) (baseStart_6972425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972425 prefixEnd_6972425 := by exact prefixLift 6972425
  have htrace : WordTrace (prefixWord ++ tailWord_6972425) baseStart_6972425 baseEnd_6972425 := by
    simpa [prefixWord, tailWord_6972425, baseEnd_6972425] using wordTrace_append hprefix tailTrace_6972425
  have hstable : (prefixWord ++ tailWord_6972425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972425).length < 2 ^ (prefixWord ++ tailWord_6972425).sum := by decide
  have hdescent : baseEnd_6972425 < baseStart_6972425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972452 : List Nat := [2, 3, 1, 4, 1, 2, 2, 1, 1, 1, 5]
def baseStart_6972452 : Nat := 118140960795 + 6972452 * 2 ^ 59
def prefixEnd_6972452 : Nat := 4983230072969 + 3 ^ 40 * 6972452 * 2
def baseEnd_6972452 : Nat := 3580219216402659483184283

theorem tailTrace_6972452 : CollatzResearch.WordTrace tailWord_6972452 prefixEnd_6972452 3580219216402659483184283 := by
  unfold tailWord_6972452
  simp only [CollatzResearch.WordTrace]
  refine ⟨127153108268002339421139805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169537477690669785894853073 127153108268002339421139805)
  ·
    refine ⟨47682415600500877282927427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127153108268002339421139805 47682415600500877282927427)
    ·
      refine ⟨71523623400751315924391141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47682415600500877282927427 71523623400751315924391141)
      ·
        refine ⟨13410679387640871735823339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71523623400751315924391141 13410679387640871735823339)
        ·
          refine ⟨20116019081461307603735009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13410679387640871735823339 20116019081461307603735009)
          ·
            refine ⟨15087014311095980702801257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20116019081461307603735009 15087014311095980702801257)
            ·
              refine ⟨11315260733321985527100943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15087014311095980702801257 11315260733321985527100943)
              ·
                refine ⟨16972891099982978290651415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11315260733321985527100943 16972891099982978290651415)
                ·
                  refine ⟨25459336649974467435977123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16972891099982978290651415 25459336649974467435977123)
                  ·
                    refine ⟨38189004974961701153965685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25459336649974467435977123 38189004974961701153965685)
                    ·
                      refine ⟨3580219216402659483184283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38189004974961701153965685 3580219216402659483184283)
                      ·
                        rfl

theorem cell23_6972452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_6972452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972452 prefixEnd_6972452 := by exact prefixLift 6972452
  have htrace : WordTrace (prefixWord ++ tailWord_6972452) baseStart_6972452 baseEnd_6972452 := by
    simpa [prefixWord, tailWord_6972452, baseEnd_6972452] using wordTrace_append hprefix tailTrace_6972452
  have hstable : (prefixWord ++ tailWord_6972452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972452).length < 2 ^ (prefixWord ++ tailWord_6972452).sum := by decide
  have hdescent : baseEnd_6972452 < baseStart_6972452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972455 : List Nat := [1, 1, 7, 1, 1, 1, 11]
def baseStart_6972455 : Nat := 118140960795 + 6972455 * 2 ^ 59
def prefixEnd_6972455 : Nat := 4983230072969 + 3 ^ 40 * 6972455 * 2
def baseEnd_6972455 : Nat := 44200256257341024338849

theorem tailTrace_6972455 : CollatzResearch.WordTrace tailWord_6972455 prefixEnd_6972455 44200256257341024338849 := by
  unfold tailWord_6972455
  simp only [CollatzResearch.WordTrace]
  refine ⟨254306325954993810354638819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169537550636662540236425879 254306325954993810354638819)
  ·
    refine ⟨381459488932490715531958229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254306325954993810354638819 381459488932490715531958229)
    ·
      refine ⟨8940456771855251145280271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 381459488932490715531958229 8940456771855251145280271)
      ·
        refine ⟨13410685157782876717920407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8940456771855251145280271 13410685157782876717920407)
        ·
          refine ⟨20116027736674315076880611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13410685157782876717920407 20116027736674315076880611)
          ·
            refine ⟨30174041605011472615320917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20116027736674315076880611 30174041605011472615320917)
            ·
              refine ⟨44200256257341024338849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 30174041605011472615320917 44200256257341024338849)
              ·
                rfl

theorem cell23_6972455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 11].length) (baseStart_6972455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972455 prefixEnd_6972455 := by exact prefixLift 6972455
  have htrace : WordTrace (prefixWord ++ tailWord_6972455) baseStart_6972455 baseEnd_6972455 := by
    simpa [prefixWord, tailWord_6972455, baseEnd_6972455] using wordTrace_append hprefix tailTrace_6972455
  have hstable : (prefixWord ++ tailWord_6972455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972455).length < 2 ^ (prefixWord ++ tailWord_6972455).sum := by decide
  have hdescent : baseEnd_6972455 < baseStart_6972455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972486 : List Nat := [6, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3]
def baseStart_6972486 : Nat := 118140960795 + 6972486 * 2 ^ 59
def prefixEnd_6972486 : Nat := 4983230072969 + 3 ^ 40 * 6972486 * 2
def baseEnd_6972486 : Nat := 3580236674744912350159127

theorem tailTrace_6972486 : CollatzResearch.WordTrace tailWord_6972486 prefixEnd_6972486 3580236674744912350159127 := by
  unfold tailWord_6972486
  simp only [CollatzResearch.WordTrace]
  refine ⟨7947108019308796957781791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 169538304411921001766011541 7947108019308796957781791)
  ·
    refine ⟨11920662028963195436672687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7947108019308796957781791 11920662028963195436672687)
    ·
      refine ⟨17880993043444793155009031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11920662028963195436672687 17880993043444793155009031)
      ·
        refine ⟨26821489565167189732513547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17880993043444793155009031 26821489565167189732513547)
        ·
          refine ⟨40232234347750784598770321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26821489565167189732513547 40232234347750784598770321)
          ·
            refine ⟨30174175760813088449077741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40232234347750784598770321 30174175760813088449077741)
            ·
              refine ⟨11315315910304908168404153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30174175760813088449077741 11315315910304908168404153)
              ·
                refine ⟨8486486932728681126303115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11315315910304908168404153 8486486932728681126303115)
                ·
                  refine ⟨12729730399093021689454673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8486486932728681126303115 12729730399093021689454673)
                  ·
                    refine ⟨9547297799319766267091005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12729730399093021689454673 9547297799319766267091005)
                    ·
                      refine ⟨3580236674744912350159127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9547297799319766267091005 3580236674744912350159127)
                      ·
                        rfl

theorem cell23_6972486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_6972486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972486 prefixEnd_6972486 := by exact prefixLift 6972486
  have htrace : WordTrace (prefixWord ++ tailWord_6972486) baseStart_6972486 baseEnd_6972486 := by
    simpa [prefixWord, tailWord_6972486, baseEnd_6972486] using wordTrace_append hprefix tailTrace_6972486
  have hstable : (prefixWord ++ tailWord_6972486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972486).length < 2 ^ (prefixWord ++ tailWord_6972486).sum := by decide
  have hdescent : baseEnd_6972486 < baseStart_6972486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972535 : List Nat := [1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 4]
def baseStart_6972535 : Nat := 118140960795 + 6972535 * 2 ^ 59
def prefixEnd_6972535 : Nat := 4983230072969 + 3 ^ 40 * 6972535 * 2
def baseEnd_6972535 : Nat := 3580261835296982658446401

theorem tailTrace_6972535 : CollatzResearch.WordTrace tailWord_6972535 prefixEnd_6972535 3580261835296982658446401 := by
  unfold tailWord_6972535
  simp only [CollatzResearch.WordTrace]
  refine ⟨254309243794703984017551059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169539495863135989345034039 254309243794703984017551059)
  ·
    refine ⟨381463865692055976026326589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254309243794703984017551059 381463865692055976026326589)
    ·
      refine ⟨143048949634520991009872471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 381463865692055976026326589 143048949634520991009872471)
      ·
        refine ⟨214573424451781486514808707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143048949634520991009872471 214573424451781486514808707)
        ·
          refine ⟨321860136677672229772213061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214573424451781486514808707 321860136677672229772213061)
          ·
            refine ⟨60348775627063543082289949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 321860136677672229772213061 60348775627063543082289949)
            ·
              refine ⟨22630790860148828655858731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60348775627063543082289949 22630790860148828655858731)
              ·
                refine ⟨33946186290223242983788097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22630790860148828655858731 33946186290223242983788097)
                ·
                  refine ⟨25459639717667432237841073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33946186290223242983788097 25459639717667432237841073)
                  ·
                    refine ⟨19094729788250574178380805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25459639717667432237841073 19094729788250574178380805)
                    ·
                      refine ⟨3580261835296982658446401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19094729788250574178380805 3580261835296982658446401)
                      ·
                        rfl

theorem cell23_6972535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_6972535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972535 prefixEnd_6972535 := by exact prefixLift 6972535
  have htrace : WordTrace (prefixWord ++ tailWord_6972535) baseStart_6972535 baseEnd_6972535 := by
    simpa [prefixWord, tailWord_6972535, baseEnd_6972535] using wordTrace_append hprefix tailTrace_6972535
  have hstable : (prefixWord ++ tailWord_6972535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972535).length < 2 ^ (prefixWord ++ tailWord_6972535).sum := by decide
  have hdescent : baseEnd_6972535 < baseStart_6972535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972545 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 9]
def baseStart_6972545 : Nat := 118140960795 + 6972545 * 2 ^ 59
def prefixEnd_6972545 : Nat := 4983230072969 + 3 ^ 40 * 6972545 * 2
def baseEnd_6972545 : Nat := 397807441122614179924595

theorem tailTrace_6972545 : CollatzResearch.WordTrace tailWord_6972545 prefixEnd_6972545 397807441122614179924595 := by
  unfold tailWord_6972545
  simp only [CollatzResearch.WordTrace]
  refine ⟨254309608524667755725415089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169539739016445170483610059 254309608524667755725415089)
  ·
    refine ⟨190732206393500816794061317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254309608524667755725415089 190732206393500816794061317)
    ·
      refine ⟨35762288698781403148886497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190732206393500816794061317 35762288698781403148886497)
      ·
        refine ⟨26821716524086052361664873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35762288698781403148886497 26821716524086052361664873)
        ·
          refine ⟨20116287393064539271248655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26821716524086052361664873 20116287393064539271248655)
          ·
            refine ⟨30174431089596808906872983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20116287393064539271248655 30174431089596808906872983)
            ·
              refine ⟨45261646634395213360309475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30174431089596808906872983 45261646634395213360309475)
              ·
                refine ⟨67892469951592820040464213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45261646634395213360309475 67892469951592820040464213)
                ·
                  refine ⟨397807441122614179924595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67892469951592820040464213 397807441122614179924595)
                  ·
                    rfl

theorem cell23_6972545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 9].length) (baseStart_6972545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972545 prefixEnd_6972545 := by exact prefixLift 6972545
  have htrace : WordTrace (prefixWord ++ tailWord_6972545) baseStart_6972545 baseEnd_6972545 := by
    simpa [prefixWord, tailWord_6972545, baseEnd_6972545] using wordTrace_append hprefix tailTrace_6972545
  have hstable : (prefixWord ++ tailWord_6972545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972545).length < 2 ^ (prefixWord ++ tailWord_6972545).sum := by decide
  have hdescent : baseEnd_6972545 < baseStart_6972545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972572 : List Nat := [2, 2, 3, 2, 1, 2, 1, 2, 2, 3, 3]
def baseStart_6972572 : Nat := 118140960795 + 6972572 * 2 ^ 59
def prefixEnd_6972572 : Nat := 4983230072969 + 3 ^ 40 * 6972572 * 2
def baseEnd_6972572 : Nat := 3580280834081199013683731

theorem tailTrace_6972572 : CollatzResearch.WordTrace tailWord_6972572 prefixEnd_6972572 3580280834081199013683731 := by
  unfold tailWord_6972572
  simp only [CollatzResearch.WordTrace]
  refine ⟨127155296647784969668323985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169540395530379959557765313 127155296647784969668323985)
  ·
    refine ⟨95366472485838727251242989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127155296647784969668323985 95366472485838727251242989)
    ·
      refine ⟨35762427182189522719216121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95366472485838727251242989 35762427182189522719216121)
      ·
        refine ⟨26821820386642142039412091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35762427182189522719216121 26821820386642142039412091)
        ·
          refine ⟨40232730579963213059118137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26821820386642142039412091 40232730579963213059118137)
          ·
            refine ⟨30174547934972409794338603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40232730579963213059118137 30174547934972409794338603)
            ·
              refine ⟨45261821902458614691507905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30174547934972409794338603 45261821902458614691507905)
              ·
                refine ⟨33946366426843961018630929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45261821902458614691507905 33946366426843961018630929)
                ·
                  refine ⟨25459774820132970763973197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33946366426843961018630929 25459774820132970763973197)
                  ·
                    refine ⟨9547415557549864036489949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25459774820132970763973197 9547415557549864036489949)
                    ·
                      refine ⟨3580280834081199013683731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9547415557549864036489949 3580280834081199013683731)
                      ·
                        rfl

theorem cell23_6972572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_6972572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972572 prefixEnd_6972572 := by exact prefixLift 6972572
  have htrace : WordTrace (prefixWord ++ tailWord_6972572) baseStart_6972572 baseEnd_6972572 := by
    simpa [prefixWord, tailWord_6972572, baseEnd_6972572] using wordTrace_append hprefix tailTrace_6972572
  have hstable : (prefixWord ++ tailWord_6972572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972572).length < 2 ^ (prefixWord ++ tailWord_6972572).sum := by decide
  have hdescent : baseEnd_6972572 < baseStart_6972572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972595 : List Nat := [1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 4]
def baseStart_6972595 : Nat := 118140960795 + 6972595 * 2 ^ 59
def prefixEnd_6972595 : Nat := 4983230072969 + 3 ^ 40 * 6972595 * 2
def baseEnd_6972595 : Nat := 3580292644136252423696125

theorem tailTrace_6972595 : CollatzResearch.WordTrace tailWord_6972595 prefixEnd_6972595 3580292644136252423696125 := by
  unfold tailWord_6972595
  simp only [CollatzResearch.WordTrace]
  refine ⟨254311432174486614264735239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169540954782991076176490159 254311432174486614264735239)
  ·
    refine ⟨381467148261729921397102859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254311432174486614264735239 381467148261729921397102859)
    ·
      refine ⟨572200722392594882095654289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381467148261729921397102859 572200722392594882095654289)
      ·
        refine ⟨429150541794446161571740717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 572200722392594882095654289 429150541794446161571740717)
        ·
          refine ⟨160931453172917310589402769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 429150541794446161571740717 160931453172917310589402769)
          ·
            refine ⟨120698589879687982942052077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160931453172917310589402769 120698589879687982942052077)
            ·
              refine ⟨45261971204882993603269529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120698589879687982942052077 45261971204882993603269529)
              ·
                refine ⟨33946478403662245202452147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45261971204882993603269529 33946478403662245202452147)
                ·
                  refine ⟨50919717605493367803678221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33946478403662245202452147 50919717605493367803678221)
                  ·
                    refine ⟨19094894102060012926379333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50919717605493367803678221 19094894102060012926379333)
                    ·
                      refine ⟨3580292644136252423696125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19094894102060012926379333 3580292644136252423696125)
                      ·
                        rfl

theorem cell23_6972595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 4].length) (baseStart_6972595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972595 prefixEnd_6972595 := by exact prefixLift 6972595
  have htrace : WordTrace (prefixWord ++ tailWord_6972595) baseStart_6972595 baseEnd_6972595 := by
    simpa [prefixWord, tailWord_6972595, baseEnd_6972595] using wordTrace_append hprefix tailTrace_6972595
  have hstable : (prefixWord ++ tailWord_6972595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972595).length < 2 ^ (prefixWord ++ tailWord_6972595).sum := by decide
  have hdescent : baseEnd_6972595 < baseStart_6972595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972629 : List Nat := [1, 3, 2, 4, 1, 2, 1, 2, 2, 1, 4]
def baseStart_6972629 : Nat := 118140960795 + 6972629 * 2 ^ 59
def prefixEnd_6972629 : Nat := 4983230072969 + 3 ^ 40 * 6972629 * 2
def baseEnd_6972629 : Nat := 3580310102478505290670969

theorem tailTrace_6972629 : CollatzResearch.WordTrace tailWord_6972629 prefixEnd_6972629 3580310102478505290670969 := by
  unfold tailWord_6972629
  simp only [CollatzResearch.WordTrace]
  refine ⟨254312672256363438071472941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169541781504242292047648627 254312672256363438071472941)
  ·
    refine ⟨95367252096136289276802353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254312672256363438071472941 95367252096136289276802353)
    ·
      refine ⟨71525439072102216957601765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95367252096136289276802353 71525439072102216957601765)
      ·
        refine ⟨13411019826019165679550331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71525439072102216957601765 13411019826019165679550331)
        ·
          refine ⟨20116529739028748519325497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13411019826019165679550331 20116529739028748519325497)
          ·
            refine ⟨15087397304271561389494123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20116529739028748519325497 15087397304271561389494123)
            ·
              refine ⟨22631095956407342084241185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15087397304271561389494123 22631095956407342084241185)
              ·
                refine ⟨16973321967305506563180889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22631095956407342084241185 16973321967305506563180889)
                ·
                  refine ⟨12729991475479129922385667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16973321967305506563180889 12729991475479129922385667)
                  ·
                    refine ⟨19094987213218694883578501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12729991475479129922385667 19094987213218694883578501)
                    ·
                      refine ⟨3580310102478505290670969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19094987213218694883578501 3580310102478505290670969)
                      ·
                        rfl

theorem cell23_6972629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_6972629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972629 prefixEnd_6972629 := by exact prefixLift 6972629
  have htrace : WordTrace (prefixWord ++ tailWord_6972629) baseStart_6972629 baseEnd_6972629 := by
    simpa [prefixWord, tailWord_6972629, baseEnd_6972629] using wordTrace_append hprefix tailTrace_6972629
  have hstable : (prefixWord ++ tailWord_6972629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972629).length < 2 ^ (prefixWord ++ tailWord_6972629).sum := by decide
  have hdescent : baseEnd_6972629 < baseStart_6972629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972639 : List Nat := [1, 1, 2, 3, 2, 1, 2, 6, 1, 4]
def baseStart_6972639 : Nat := 118140960795 + 6972639 * 2 ^ 59
def prefixEnd_6972639 : Nat := 4983230072969 + 3 ^ 40 * 6972639 * 2
def baseEnd_6972639 : Nat := 1193438412428350083848641

theorem tailTrace_6972639 : CollatzResearch.WordTrace tailWord_6972639 prefixEnd_6972639 1193438412428350083848641 := by
  unfold tailWord_6972639
  simp only [CollatzResearch.WordTrace]
  refine ⟨254313036986327209779336971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169542024657551473186224647 254313036986327209779336971)
  ·
    refine ⟨381469555479490814669005457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254313036986327209779336971 381469555479490814669005457)
    ·
      refine ⟨286102166609618111001754093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381469555479490814669005457 286102166609618111001754093)
      ·
        refine ⟨107288312478606791625657785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286102166609618111001754093 107288312478606791625657785)
        ·
          refine ⟨80466234358955093719243339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107288312478606791625657785 80466234358955093719243339)
          ·
            refine ⟨120699351538432640578865009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80466234358955093719243339 120699351538432640578865009)
            ·
              refine ⟨90524513653824480434148757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120699351538432640578865009 90524513653824480434148757)
              ·
                refine ⟨4243336577523022520350723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90524513653824480434148757 4243336577523022520350723)
                ·
                  refine ⟨6365004866284533780526085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4243336577523022520350723 6365004866284533780526085)
                  ·
                    refine ⟨1193438412428350083848641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6365004866284533780526085 1193438412428350083848641)
                    ·
                      rfl

theorem cell23_6972639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 6, 1, 4].length) (baseStart_6972639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972639 prefixEnd_6972639 := by exact prefixLift 6972639
  have htrace : WordTrace (prefixWord ++ tailWord_6972639) baseStart_6972639 baseEnd_6972639 := by
    simpa [prefixWord, tailWord_6972639, baseEnd_6972639] using wordTrace_append hprefix tailTrace_6972639
  have hstable : (prefixWord ++ tailWord_6972639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972639).length < 2 ^ (prefixWord ++ tailWord_6972639).sum := by decide
  have hdescent : baseEnd_6972639 < baseStart_6972639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972652 : List Nat := [2, 2, 1, 1, 2, 5, 1, 3, 6]
def baseStart_6972652 : Nat := 118140960795 + 6972652 * 2 ^ 59
def prefixEnd_6972652 : Nat := 4983230072969 + 3 ^ 40 * 6972652 * 2
def baseEnd_6972652 : Nat := 397813545837062077853707

theorem tailTrace_6972652 : CollatzResearch.WordTrace tailWord_6972652 prefixEnd_6972652 397813545837062077853707 := by
  unfold tailWord_6972652
  simp only [CollatzResearch.WordTrace]
  refine ⟨127156755567640056499780105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169542340756853408666373473 127156755567640056499780105)
  ·
    refine ⟨95367566675730042374835079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127156755567640056499780105 95367566675730042374835079)
    ·
      refine ⟨143051350013595063562252619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95367566675730042374835079 143051350013595063562252619)
      ·
        refine ⟨214577025020392595343378929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143051350013595063562252619 214577025020392595343378929)
        ·
          refine ⟨160932768765294446507534197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214577025020392595343378929 160932768765294446507534197)
          ·
            refine ⟨15087447071746354360081331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160932768765294446507534197 15087447071746354360081331)
            ·
              refine ⟨22631170607619531540121997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15087447071746354360081331 22631170607619531540121997)
              ·
                refine ⟨8486688977857324327545749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22631170607619531540121997 8486688977857324327545749)
                ·
                  refine ⟨397813545837062077853707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8486688977857324327545749 397813545837062077853707)
                  ·
                    rfl

theorem cell23_6972652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 6].length) (baseStart_6972652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972652 prefixEnd_6972652 := by exact prefixLift 6972652
  have htrace : WordTrace (prefixWord ++ tailWord_6972652) baseStart_6972652 baseEnd_6972652 := by
    simpa [prefixWord, tailWord_6972652, baseEnd_6972652] using wordTrace_append hprefix tailTrace_6972652
  have hstable : (prefixWord ++ tailWord_6972652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972652).length < 2 ^ (prefixWord ++ tailWord_6972652).sum := by decide
  have hdescent : baseEnd_6972652 < baseStart_6972652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972689 : List Nat := [1, 2, 2, 1, 1, 4, 1, 4, 2, 3, 2]
def baseStart_6972689 : Nat := 118140960795 + 6972689 * 2 ^ 59
def prefixEnd_6972689 : Nat := 4983230072969 + 3 ^ 40 * 6972689 * 2
def baseEnd_6972689 : Nat := 3580340911317775055920693

theorem tailTrace_6972689 : CollatzResearch.WordTrace tailWord_6972689 prefixEnd_6972689 3580340911317775055920693 := by
  unfold tailWord_6972689
  simp only [CollatzResearch.WordTrace]
  refine ⟨254314860636146068318657121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169543240424097378879104747 254314860636146068318657121)
  ·
    refine ⟨190736145477109551238992841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254314860636146068318657121 190736145477109551238992841)
    ·
      refine ⟨143052109107832163429244631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190736145477109551238992841 143052109107832163429244631)
      ·
        refine ⟨214578163661748245143866947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143052109107832163429244631 214578163661748245143866947)
        ·
          refine ⟨321867245492622367715800421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214578163661748245143866947 321867245492622367715800421)
          ·
            refine ⟨60350108529866693946712579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 321867245492622367715800421 60350108529866693946712579)
            ·
              refine ⟨90525162794800040920068869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60350108529866693946712579 90525162794800040920068869)
              ·
                refine ⟨16973468024025007672512913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90525162794800040920068869 16973468024025007672512913)
                ·
                  refine ⟨12730101018018755754384685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16973468024025007672512913 12730101018018755754384685)
                  ·
                    refine ⟨4773787881757033407894257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12730101018018755754384685 4773787881757033407894257)
                    ·
                      refine ⟨3580340911317775055920693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4773787881757033407894257 3580340911317775055920693)
                      ·
                        rfl

theorem cell23_6972689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 3, 2].length) (baseStart_6972689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972689 prefixEnd_6972689 := by exact prefixLift 6972689
  have htrace : WordTrace (prefixWord ++ tailWord_6972689) baseStart_6972689 baseEnd_6972689 := by
    simpa [prefixWord, tailWord_6972689, baseEnd_6972689] using wordTrace_append hprefix tailTrace_6972689
  have hstable : (prefixWord ++ tailWord_6972689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972689).length < 2 ^ (prefixWord ++ tailWord_6972689).sum := by decide
  have hdescent : baseEnd_6972689 < baseStart_6972689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972690 : List Nat := [3, 2, 4, 2, 1, 1, 1, 4, 1, 4]
def baseStart_6972690 : Nat := 118140960795 + 6972690 * 2 ^ 59
def prefixEnd_6972690 : Nat := 4983230072969 + 3 ^ 40 * 6972690 * 2
def baseEnd_6972690 : Nat := 1193447141599476517336063

theorem tailTrace_6972690 : CollatzResearch.WordTrace tailWord_6972690 prefixEnd_6972690 1193447141599476517336063 := by
  unfold tailWord_6972690
  simp only [CollatzResearch.WordTrace]
  refine ⟨63578724277285611372360881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169543264739428296992962349 63578724277285611372360881)
  ·
    refine ⟨47684043207964208529270661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63578724277285611372360881 47684043207964208529270661)
    ·
      refine ⟨8940758101493289099238249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47684043207964208529270661 8940758101493289099238249)
      ·
        refine ⟨6705568576119966824428687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8940758101493289099238249 6705568576119966824428687)
        ·
          refine ⟨10058352864179950236643031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6705568576119966824428687 10058352864179950236643031)
          ·
            refine ⟨15087529296269925354964547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10058352864179950236643031 15087529296269925354964547)
            ·
              refine ⟨22631293944404888032446821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15087529296269925354964547 22631293944404888032446821)
              ·
                refine ⟨4243367614575916506083779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22631293944404888032446821 4243367614575916506083779)
                ·
                  refine ⟨6365051421863874759125669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4243367614575916506083779 6365051421863874759125669)
                  ·
                    refine ⟨1193447141599476517336063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6365051421863874759125669 1193447141599476517336063)
                    ·
                      rfl

theorem cell23_6972690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_6972690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972690 prefixEnd_6972690 := by exact prefixLift 6972690
  have htrace : WordTrace (prefixWord ++ tailWord_6972690) baseStart_6972690 baseEnd_6972690 := by
    simpa [prefixWord, tailWord_6972690, baseEnd_6972690] using wordTrace_append hprefix tailTrace_6972690
  have hstable : (prefixWord ++ tailWord_6972690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972690).length < 2 ^ (prefixWord ++ tailWord_6972690).sum := by decide
  have hdescent : baseEnd_6972690 < baseStart_6972690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972753 : List Nat := [1, 2, 2, 1, 4, 1, 1, 6, 1, 2, 2]
def baseStart_6972753 : Nat := 118140960795 + 6972753 * 2 ^ 59
def prefixEnd_6972753 : Nat := 4983230072969 + 3 ^ 40 * 6972753 * 2
def baseEnd_6972753 : Nat := 3580373774079662805520399

theorem tailTrace_6972753 : CollatzResearch.WordTrace tailWord_6972753 prefixEnd_6972753 3580373774079662805520399 := by
  unfold tailWord_6972753
  simp only [CollatzResearch.WordTrace]
  refine ⟨254317194907914207248986913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169544796605276138165991275 254317194907914207248986913)
  ·
    refine ⟨190737896180935655436740185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254317194907914207248986913 190737896180935655436740185)
    ·
      refine ⟨143053422135701741577555139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190737896180935655436740185 143053422135701741577555139)
      ·
        refine ⟨214580133203552612366332709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143053422135701741577555139 214580133203552612366332709)
        ·
          refine ⟨40233774975666114818687383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214580133203552612366332709 40233774975666114818687383)
          ·
            refine ⟨60350662463499172228031075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40233774975666114818687383 60350662463499172228031075)
            ·
              refine ⟨90525993695248758342046613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60350662463499172228031075 90525993695248758342046613)
              ·
                refine ⟨4243405954464785547283435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90525993695248758342046613 4243405954464785547283435)
                ·
                  refine ⟨6365108931697178320925153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4243405954464785547283435 6365108931697178320925153)
                  ·
                    refine ⟨4773831698772883740693865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6365108931697178320925153 4773831698772883740693865)
                    ·
                      refine ⟨3580373774079662805520399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4773831698772883740693865 3580373774079662805520399)
                      ·
                        rfl

theorem cell23_6972753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 6, 1, 2, 2].length) (baseStart_6972753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972753 prefixEnd_6972753 := by exact prefixLift 6972753
  have htrace : WordTrace (prefixWord ++ tailWord_6972753) baseStart_6972753 baseEnd_6972753 := by
    simpa [prefixWord, tailWord_6972753, baseEnd_6972753] using wordTrace_append hprefix tailTrace_6972753
  have hstable : (prefixWord ++ tailWord_6972753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972753).length < 2 ^ (prefixWord ++ tailWord_6972753).sum := by decide
  have hdescent : baseEnd_6972753 < baseStart_6972753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972776 : List Nat := [2, 1, 4, 2, 3, 2, 2, 7]
def baseStart_6972776 : Nat := 118140960795 + 6972776 * 2 ^ 59
def prefixEnd_6972776 : Nat := 4983230072969 + 3 ^ 40 * 6972776 * 2
def baseEnd_6972776 : Nat := 132606873486470970945659

theorem tailTrace_6972776 : CollatzResearch.WordTrace tailWord_6972776 prefixEnd_6972776 132606873486470970945659 := by
  unfold tailWord_6972776
  simp only [CollatzResearch.WordTrace]
  refine ⟨127159016893415441088537091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169545355857887254784716121 127159016893415441088537091)
  ·
    refine ⟨190738525340123161632805637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127159016893415441088537091 190738525340123161632805637)
    ·
      refine ⟨35763473501273092806151057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190738525340123161632805637 35763473501273092806151057)
      ·
        refine ⟨26822605125954819604613293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35763473501273092806151057 26822605125954819604613293)
        ·
          refine ⟨10058476922233057351729985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26822605125954819604613293 10058476922233057351729985)
          ·
            refine ⟨7543857691674793013797489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10058476922233057351729985 7543857691674793013797489)
            ·
              refine ⟨5657893268756094760348117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7543857691674793013797489 5657893268756094760348117)
              ·
                refine ⟨132606873486470970945659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5657893268756094760348117 132606873486470970945659)
                ·
                  rfl

theorem cell23_6972776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 7].length) (baseStart_6972776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972776 prefixEnd_6972776 := by exact prefixLift 6972776
  have htrace : WordTrace (prefixWord ++ tailWord_6972776) baseStart_6972776 baseEnd_6972776 := by
    simpa [prefixWord, tailWord_6972776, baseEnd_6972776] using wordTrace_append hprefix tailTrace_6972776
  have hstable : (prefixWord ++ tailWord_6972776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972776).length < 2 ^ (prefixWord ++ tailWord_6972776).sum := by decide
  have hdescent : baseEnd_6972776 < baseStart_6972776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972796 : List Nat := [2, 2, 2, 1, 1, 1, 3, 5, 1, 3, 2]
def baseStart_6972796 : Nat := 118140960795 + 6972796 * 2 ^ 59
def prefixEnd_6972796 : Nat := 4983230072969 + 3 ^ 40 * 6972796 * 2
def baseEnd_6972796 : Nat := 3580395853747806137282701

theorem tailTrace_6972796 : CollatzResearch.WordTrace tailWord_6972796 prefixEnd_6972796 3580395853747806137282701 := by
  unfold tailWord_6972796
  simp only [CollatzResearch.WordTrace]
  refine ⟨127159381623379212796401121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169545842164505617061868161 127159381623379212796401121)
  ·
    refine ⟨95369536217534409597300841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127159381623379212796401121 95369536217534409597300841)
    ·
      refine ⟨71527152163150807197975631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95369536217534409597300841 71527152163150807197975631)
      ·
        refine ⟨107290728244726210796963447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71527152163150807197975631 107290728244726210796963447)
        ·
          refine ⟨160936092367089316195445171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107290728244726210796963447 160936092367089316195445171)
          ·
            refine ⟨241404138550633974293167757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160936092367089316195445171 241404138550633974293167757)
            ·
              refine ⟨90526551956487740359937909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241404138550633974293167757 90526551956487740359937909)
              ·
                refine ⟨8486864245920725658744179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90526551956487740359937909 8486864245920725658744179)
                ·
                  refine ⟨12730296368881088488116269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8486864245920725658744179 12730296368881088488116269)
                  ·
                    refine ⟨4773861138330408183043601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12730296368881088488116269 4773861138330408183043601)
                    ·
                      refine ⟨3580395853747806137282701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4773861138330408183043601 3580395853747806137282701)
                      ·
                        rfl

theorem cell23_6972796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 1, 3, 2].length) (baseStart_6972796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972796 prefixEnd_6972796 := by exact prefixLift 6972796
  have htrace : WordTrace (prefixWord ++ tailWord_6972796) baseStart_6972796 baseEnd_6972796 := by
    simpa [prefixWord, tailWord_6972796, baseEnd_6972796] using wordTrace_append hprefix tailTrace_6972796
  have hstable : (prefixWord ++ tailWord_6972796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972796).length < 2 ^ (prefixWord ++ tailWord_6972796).sum := by decide
  have hdescent : baseEnd_6972796 < baseStart_6972796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972812 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 1, 3, 5]
def baseStart_6972812 : Nat := 118140960795 + 6972812 * 2 ^ 59
def prefixEnd_6972812 : Nat := 4983230072969 + 3 ^ 40 * 6972812 * 2
def baseEnd_6972812 : Nat := 3580404069438278074682627

theorem tailTrace_6972812 : CollatzResearch.WordTrace tailWord_6972812 prefixEnd_6972812 3580404069438278074682627 := by
  unfold tailWord_6972812
  simp only [CollatzResearch.WordTrace]
  refine ⟨127159673407350230162692345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169546231209800306883589793 127159673407350230162692345)
  ·
    refine ⟨95369755055512672622019259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127159673407350230162692345 95369755055512672622019259)
    ·
      refine ⟨143054632583269008933028889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95369755055512672622019259 143054632583269008933028889)
      ·
        refine ⟨107290974437451756699771667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143054632583269008933028889 107290974437451756699771667)
        ·
          refine ⟨160936461656177635049657501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107290974437451756699771667 160936461656177635049657501)
          ·
            refine ⟨60351173121066613143621563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160936461656177635049657501 60351173121066613143621563)
            ·
              refine ⟨90526759681599919715432345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60351173121066613143621563 90526759681599919715432345)
              ·
                refine ⟨67895069761199939786574259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90526759681599919715432345 67895069761199939786574259)
                ·
                  refine ⟨101842604641799909679861389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67895069761199939786574259 101842604641799909679861389)
                  ·
                    refine ⟨38190976740674966129948021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101842604641799909679861389 38190976740674966129948021)
                    ·
                      refine ⟨3580404069438278074682627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38190976740674966129948021 3580404069438278074682627)
                      ·
                        rfl

theorem cell23_6972812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_6972812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972812 prefixEnd_6972812 := by exact prefixLift 6972812
  have htrace : WordTrace (prefixWord ++ tailWord_6972812) baseStart_6972812 baseEnd_6972812 := by
    simpa [prefixWord, tailWord_6972812, baseEnd_6972812] using wordTrace_append hprefix tailTrace_6972812
  have hstable : (prefixWord ++ tailWord_6972812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972812).length < 2 ^ (prefixWord ++ tailWord_6972812).sum := by decide
  have hdescent : baseEnd_6972812 < baseStart_6972812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972820 : List Nat := [2, 4, 2, 1, 2, 1, 4, 1, 2, 1, 3]
def baseStart_6972820 : Nat := 118140960795 + 6972820 * 2 ^ 59
def prefixEnd_6972820 : Nat := 4983230072969 + 3 ^ 40 * 6972820 * 2
def baseEnd_6972820 : Nat := 3580408177283514043382591

theorem tailTrace_6972820 : CollatzResearch.WordTrace tailWord_6972820 prefixEnd_6972820 3580408177283514043382591 := by
  unfold tailWord_6972820
  simp only [CollatzResearch.WordTrace]
  refine ⟨127159819299335738845837957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169546425732447651794450609 127159819299335738845837957)
  ·
    refine ⟨23842466118625451033594617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127159819299335738845837957 23842466118625451033594617)
    ·
      refine ⟨17881849588969088275195963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23842466118625451033594617 17881849588969088275195963)
      ·
        refine ⟨26822774383453632412793945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17881849588969088275195963 26822774383453632412793945)
        ·
          refine ⟨20117080787590224309595459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26822774383453632412793945 20117080787590224309595459)
          ·
            refine ⟨30175621181385336464393189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20117080787590224309595459 30175621181385336464393189)
            ·
              refine ⟨5657928971509750587073723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30175621181385336464393189 5657928971509750587073723)
              ·
                refine ⟨8486893457264625880610585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5657928971509750587073723 8486893457264625880610585)
                ·
                  refine ⟨6365170092948469410457939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8486893457264625880610585 6365170092948469410457939)
                  ·
                    refine ⟨9547755139422704115686909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6365170092948469410457939 9547755139422704115686909)
                    ·
                      refine ⟨3580408177283514043382591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9547755139422704115686909 3580408177283514043382591)
                      ·
                        rfl

theorem cell23_6972820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_6972820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972820 prefixEnd_6972820 := by exact prefixLift 6972820
  have htrace : WordTrace (prefixWord ++ tailWord_6972820) baseStart_6972820 baseEnd_6972820 := by
    simpa [prefixWord, tailWord_6972820, baseEnd_6972820] using wordTrace_append hprefix tailTrace_6972820
  have hstable : (prefixWord ++ tailWord_6972820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972820).length < 2 ^ (prefixWord ++ tailWord_6972820).sum := by decide
  have hdescent : baseEnd_6972820 < baseStart_6972820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972826 : List Nat := [3, 1, 1, 4, 1, 1, 2, 3, 1, 4, 2]
def baseStart_6972826 : Nat := 118140960795 + 6972826 * 2 ^ 59
def prefixEnd_6972826 : Nat := 4983230072969 + 3 ^ 40 * 6972826 * 2
def baseEnd_6972826 : Nat := 3580411258167441019907563

theorem tailTrace_6972826 : CollatzResearch.WordTrace tailWord_6972826 prefixEnd_6972826 3580411258167441019907563 := by
  unfold tailWord_6972826
  simp only [CollatzResearch.WordTrace]
  refine ⟨63579964359162435179098583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169546571624433160477596221 63579964359162435179098583)
  ·
    refine ⟨95369946538743652768647875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63579964359162435179098583 95369946538743652768647875)
    ·
      refine ⟨143054919808115479152971813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95369946538743652768647875 143054919808115479152971813)
      ·
        refine ⟨26822797464021652341182215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143054919808115479152971813 26822797464021652341182215)
        ·
          refine ⟨40234196196032478511773323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26822797464021652341182215 40234196196032478511773323)
          ·
            refine ⟨60351294294048717767659985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40234196196032478511773323 60351294294048717767659985)
            ·
              refine ⟨45263470720536538325744989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60351294294048717767659985 45263470720536538325744989)
              ·
                refine ⟨16973801520201201872154371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45263470720536538325744989 16973801520201201872154371)
                ·
                  refine ⟨25460702280301802808231557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16973801520201201872154371 25460702280301802808231557)
                  ·
                    refine ⟨4773881677556588026543417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25460702280301802808231557 4773881677556588026543417)
                    ·
                      refine ⟨3580411258167441019907563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4773881677556588026543417 3580411258167441019907563)
                      ·
                        rfl

theorem cell23_6972826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_6972826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972826 prefixEnd_6972826 := by exact prefixLift 6972826
  have htrace : WordTrace (prefixWord ++ tailWord_6972826) baseStart_6972826 baseEnd_6972826 := by
    simpa [prefixWord, tailWord_6972826, baseEnd_6972826] using wordTrace_append hprefix tailTrace_6972826
  have hstable : (prefixWord ++ tailWord_6972826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972826).length < 2 ^ (prefixWord ++ tailWord_6972826).sum := by decide
  have hdescent : baseEnd_6972826 < baseStart_6972826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972829 : List Nat := [1, 4, 2, 1, 3, 1, 1, 2, 2, 1, 5]
def baseStart_6972829 : Nat := 118140960795 + 6972829 * 2 ^ 59
def prefixEnd_6972829 : Nat := 4983230072969 + 3 ^ 40 * 6972829 * 2
def baseEnd_6972829 : Nat := 3580412798609404508170049

theorem tailTrace_6972829 : CollatzResearch.WordTrace tailWord_6972829 prefixEnd_6972829 3580412798609404508170049 := by
  unfold tailWord_6972829
  simp only [CollatzResearch.WordTrace]
  refine ⟨254319966855638872228753541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169546644570425914819169027 254319966855638872228753541)
  ·
    refine ⟨47684993785432288542891289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254319966855638872228753541 47684993785432288542891289)
    ·
      refine ⟨35763745339074216407168467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47684993785432288542891289 35763745339074216407168467)
      ·
        refine ⟨53645618008611324610752701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35763745339074216407168467 53645618008611324610752701)
        ·
          refine ⟨20117106753229246729032263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53645618008611324610752701 20117106753229246729032263)
          ·
            refine ⟨30175660129843870093548395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20117106753229246729032263 30175660129843870093548395)
            ·
              refine ⟨45263490194765805140322593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30175660129843870093548395 45263490194765805140322593)
              ·
                refine ⟨33947617646074353855241945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45263490194765805140322593 33947617646074353855241945)
                ·
                  refine ⟨25460713234555765391431459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33947617646074353855241945 25460713234555765391431459)
                  ·
                    refine ⟨38191069851833648087147189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25460713234555765391431459 38191069851833648087147189)
                    ·
                      refine ⟨3580412798609404508170049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38191069851833648087147189 3580412798609404508170049)
                      ·
                        rfl

theorem cell23_6972829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_6972829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972829 prefixEnd_6972829 := by exact prefixLift 6972829
  have htrace : WordTrace (prefixWord ++ tailWord_6972829) baseStart_6972829 baseEnd_6972829 := by
    simpa [prefixWord, tailWord_6972829, baseEnd_6972829] using wordTrace_append hprefix tailTrace_6972829
  have hstable : (prefixWord ++ tailWord_6972829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972829).length < 2 ^ (prefixWord ++ tailWord_6972829).sum := by decide
  have hdescent : baseEnd_6972829 < baseStart_6972829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972830 : List Nat := [4, 3, 1, 2, 2, 1, 1, 1, 3, 3, 2]
def baseStart_6972830 : Nat := 118140960795 + 6972830 * 2 ^ 59
def prefixEnd_6972830 : Nat := 4983230072969 + 3 ^ 40 * 6972830 * 2
def baseEnd_6972830 : Nat := 3580413312090059004257545

theorem tailTrace_6972830 : CollatzResearch.WordTrace tailWord_6972830 prefixEnd_6972830 3580413312090059004257545 := by
  unfold tailWord_6972830
  simp only [CollatzResearch.WordTrace]
  refine ⟨31790000416079406174942493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169546668885756832933026629 31790000416079406174942493)
  ·
    refine ⟨11921250156029777315603435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31790000416079406174942493 11921250156029777315603435)
    ·
      refine ⟨17881875234044665973405153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11921250156029777315603435 17881875234044665973405153)
      ·
        refine ⟨13411406425533499480053865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17881875234044665973405153 13411406425533499480053865)
        ·
          refine ⟨10058554819150124610040399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13411406425533499480053865 10058554819150124610040399)
          ·
            refine ⟨15087832228725186915060599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10058554819150124610040399 15087832228725186915060599)
            ·
              refine ⟨22631748343087780372590899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15087832228725186915060599 22631748343087780372590899)
              ·
                refine ⟨33947622514631670558886349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22631748343087780372590899 33947622514631670558886349)
                ·
                  refine ⟨12730358442986876459582381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33947622514631670558886349 12730358442986876459582381)
                  ·
                    refine ⟨4773884416120078672343393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12730358442986876459582381 4773884416120078672343393)
                    ·
                      refine ⟨3580413312090059004257545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4773884416120078672343393 3580413312090059004257545)
                      ·
                        rfl

theorem cell23_6972830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_6972830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972830 prefixEnd_6972830 := by exact prefixLift 6972830
  have htrace : WordTrace (prefixWord ++ tailWord_6972830) baseStart_6972830 baseEnd_6972830 := by
    simpa [prefixWord, tailWord_6972830, baseEnd_6972830] using wordTrace_append hprefix tailTrace_6972830
  have hstable : (prefixWord ++ tailWord_6972830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972830).length < 2 ^ (prefixWord ++ tailWord_6972830).sum := by decide
  have hdescent : baseEnd_6972830 < baseStart_6972830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972832 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 9]
def baseStart_6972832 : Nat := 118140960795 + 6972832 * 2 ^ 59
def prefixEnd_6972832 : Nat := 4983230072969 + 3 ^ 40 * 6972832 * 2
def baseEnd_6972832 : Nat := 397823815450151999603615

theorem tailTrace_6972832 : CollatzResearch.WordTrace tailWord_6972832 prefixEnd_6972832 397823815450151999603615 := by
  unfold tailWord_6972832
  simp only [CollatzResearch.WordTrace]
  refine ⟨127160038137314001870556375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169546717516418669160741833 127160038137314001870556375)
  ·
    refine ⟨190740057205971002805834563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127160038137314001870556375 190740057205971002805834563)
    ·
      refine ⟨286110085808956504208751845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190740057205971002805834563 286110085808956504208751845)
      ·
        refine ⟨53645641089179344539140971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286110085808956504208751845 53645641089179344539140971)
        ·
          refine ⟨80468461633769016808711457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53645641089179344539140971 80468461633769016808711457)
          ·
            refine ⟨60351346225326762606533593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80468461633769016808711457 60351346225326762606533593)
            ·
              refine ⟨45263509668995071954900195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60351346225326762606533593 45263509668995071954900195)
              ·
                refine ⟨67895264503492607932350293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45263509668995071954900195 67895264503492607932350293)
                ·
                  refine ⟨397823815450151999603615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67895264503492607932350293 397823815450151999603615)
                  ·
                    rfl

theorem cell23_6972832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 9].length) (baseStart_6972832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972832 prefixEnd_6972832 := by exact prefixLift 6972832
  have htrace : WordTrace (prefixWord ++ tailWord_6972832) baseStart_6972832 baseEnd_6972832 := by
    simpa [prefixWord, tailWord_6972832, baseEnd_6972832] using wordTrace_append hprefix tailTrace_6972832
  have hstable : (prefixWord ++ tailWord_6972832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972832).length < 2 ^ (prefixWord ++ tailWord_6972832).sum := by decide
  have hdescent : baseEnd_6972832 < baseStart_6972832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972876 : List Nat := [2, 2, 1, 4, 2, 2, 1, 1, 2, 3, 3]
def baseStart_6972876 : Nat := 118140960795 + 6972876 * 2 ^ 59
def prefixEnd_6972876 : Nat := 4983230072969 + 3 ^ 40 * 6972876 * 2
def baseEnd_6972876 : Nat := 3580436932200165824282333

theorem tailTrace_6972876 : CollatzResearch.WordTrace tailWord_6972876 prefixEnd_6972876 3580436932200165824282333 := by
  unfold tailWord_6972876
  simp only [CollatzResearch.WordTrace]
  refine ⟨127160840543234299627857241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169547787390979066170476321 127160840543234299627857241)
  ·
    refine ⟨95370630407425724720892931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127160840543234299627857241 95370630407425724720892931)
    ·
      refine ⟨143055945611138587081339397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95370630407425724720892931 143055945611138587081339397)
      ·
        refine ⟨26822989802088485077751137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143055945611138587081339397 26822989802088485077751137)
        ·
          refine ⟨20117242351566363808313353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26822989802088485077751137 20117242351566363808313353)
          ·
            refine ⟨15087931763674772856235015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20117242351566363808313353 15087931763674772856235015)
            ·
              refine ⟨22631897645512159284352523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15087931763674772856235015 22631897645512159284352523)
              ·
                refine ⟨33947846468268238926528785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22631897645512159284352523 33947846468268238926528785)
                ·
                  refine ⟨25460884851201179194896589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33947846468268238926528785 25460884851201179194896589)
                  ·
                    refine ⟨9547831819200442198086221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25460884851201179194896589 9547831819200442198086221)
                    ·
                      refine ⟨3580436932200165824282333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9547831819200442198086221 3580436932200165824282333)
                      ·
                        rfl

theorem cell23_6972876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_6972876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972876 prefixEnd_6972876 := by exact prefixLift 6972876
  have htrace : WordTrace (prefixWord ++ tailWord_6972876) baseStart_6972876 baseEnd_6972876 := by
    simpa [prefixWord, tailWord_6972876, baseEnd_6972876] using wordTrace_append hprefix tailTrace_6972876
  have hstable : (prefixWord ++ tailWord_6972876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972876).length < 2 ^ (prefixWord ++ tailWord_6972876).sum := by decide
  have hdescent : baseEnd_6972876 < baseStart_6972876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972960 : List Nat := [2, 1, 1, 6, 1, 1, 3, 3, 1, 4]
def baseStart_6972960 : Nat := 118140960795 + 6972960 * 2 ^ 59
def prefixEnd_6972960 : Nat := 4983230072969 + 3 ^ 40 * 6972960 * 2
def baseEnd_6972960 : Nat := 1193493354858381165210649

theorem tailTrace_6972960 : CollatzResearch.WordTrace tailWord_6972960 prefixEnd_6972960 1193493354858381165210649 := by
  unfold tailWord_6972960
  simp only [CollatzResearch.WordTrace]
  refine ⟨127162372409082140800886167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169549829878776187734514889 127162372409082140800886167)
  ·
    refine ⟨190743558613623211201329251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127162372409082140800886167 190743558613623211201329251)
    ·
      refine ⟨286115337920434816801993877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190743558613623211201329251 286115337920434816801993877)
      ·
        refine ⟨13411656465020382037593463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 286115337920434816801993877 13411656465020382037593463)
        ·
          refine ⟨20117484697530573056390195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13411656465020382037593463 20117484697530573056390195)
          ·
            refine ⟨30176227046295859584585293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20117484697530573056390195 30176227046295859584585293)
            ·
              refine ⟨11316085142360947344219485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30176227046295859584585293 11316085142360947344219485)
              ·
                refine ⟨4243531928385355254082307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11316085142360947344219485 4243531928385355254082307)
                ·
                  refine ⟨6365297892578032881123461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4243531928385355254082307 6365297892578032881123461)
                  ·
                    refine ⟨1193493354858381165210649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6365297892578032881123461 1193493354858381165210649)
                    ·
                      rfl

theorem cell23_6972960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 3, 1, 4].length) (baseStart_6972960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972960 prefixEnd_6972960 := by exact prefixLift 6972960
  have htrace : WordTrace (prefixWord ++ tailWord_6972960) baseStart_6972960 baseEnd_6972960 := by
    simpa [prefixWord, tailWord_6972960, baseEnd_6972960] using wordTrace_append hprefix tailTrace_6972960
  have hstable : (prefixWord ++ tailWord_6972960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972960).length < 2 ^ (prefixWord ++ tailWord_6972960).sum := by decide
  have hdescent : baseEnd_6972960 < baseStart_6972960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6972983 : List Nat := [1, 1, 3, 1, 2, 4, 3, 1, 3, 1, 3]
def baseStart_6972983 : Nat := 118140960795 + 6972983 * 2 ^ 59
def prefixEnd_6972983 : Nat := 4983230072969 + 3 ^ 40 * 6972983 * 2
def baseEnd_6972983 : Nat := 3580491874630196905644341

theorem tailTrace_6972983 : CollatzResearch.WordTrace tailWord_6972983 prefixEnd_6972983 3580491874630196905644341 := by
  unfold tailWord_6972983
  simp only [CollatzResearch.WordTrace]
  refine ⟨254325583697080956529859603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169550389131387304353239735 254325583697080956529859603)
  ·
    refine ⟨381488375545621434794789405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254325583697080956529859603 381488375545621434794789405)
    ·
      refine ⟨143058140829608038048046027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 381488375545621434794789405 143058140829608038048046027)
      ·
        refine ⟨214587211244412057072069041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143058140829608038048046027 214587211244412057072069041)
        ·
          refine ⟨160940408433309042804051781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214587211244412057072069041 160940408433309042804051781)
          ·
            refine ⟨30176326581245445525759709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160940408433309042804051781 30176326581245445525759709)
            ·
              refine ⟨11316122467967042072159891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30176326581245445525759709 11316122467967042072159891)
              ·
                refine ⟨16974183701950563108239837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11316122467967042072159891 16974183701950563108239837)
                ·
                  refine ⟨6365318888231461165589939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16974183701950563108239837 6365318888231461165589939)
                  ·
                    refine ⟨9547978332347191748384909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6365318888231461165589939 9547978332347191748384909)
                    ·
                      refine ⟨3580491874630196905644341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9547978332347191748384909 3580491874630196905644341)
                      ·
                        rfl

theorem cell23_6972983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 3, 1, 3].length) (baseStart_6972983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972983 prefixEnd_6972983 := by exact prefixLift 6972983
  have htrace : WordTrace (prefixWord ++ tailWord_6972983) baseStart_6972983 baseEnd_6972983 := by
    simpa [prefixWord, tailWord_6972983, baseEnd_6972983] using wordTrace_append hprefix tailTrace_6972983
  have hstable : (prefixWord ++ tailWord_6972983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972983).length < 2 ^ (prefixWord ++ tailWord_6972983).sum := by decide
  have hdescent : baseEnd_6972983 < baseStart_6972983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
