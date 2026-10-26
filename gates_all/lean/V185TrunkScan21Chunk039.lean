import V185TrunkScan21Chunk038

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_470919 : List Nat := [1, 1, 4, 2, 4, 1, 8]
def baseStart_470919 : Nat := 118140960795 + 470919 * 2 ^ 59
def prefixEnd_470919 : Nat := 4983230072969 + 3 ^ 40 * 470919 * 2
def baseEnd_470919 : Nat := 11941125744925840046755

theorem tailTrace_470919 : CollatzResearch.WordTrace tailWord_470919 prefixEnd_470919 11941125744925840046755 := by
  unfold tailWord_470919
  simp only [CollatzResearch.WordTrace]
  refine ⟨17175826980948364407223811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11450551320632242938149207 17175826980948364407223811)
  ·
    refine ⟨25763740471422546610835717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17175826980948364407223811 25763740471422546610835717)
    ·
      refine ⟨4830701338391727489531697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25763740471422546610835717 4830701338391727489531697)
      ·
        refine ⟨3623026003793795617148773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4830701338391727489531697 3623026003793795617148773)
        ·
          refine ⟨679317375711336678215395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3623026003793795617148773 679317375711336678215395)
          ·
            refine ⟨1018976063567005017323093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 679317375711336678215395 1018976063567005017323093)
            ·
              refine ⟨11941125744925840046755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1018976063567005017323093 11941125744925840046755)
              ·
                rfl

theorem cell21_470919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 8].length) (baseStart_470919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_470919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_470919 prefixEnd_470919 := by exact prefixLift 470919
  have htrace : WordTrace (prefixWord ++ tailWord_470919) baseStart_470919 baseEnd_470919 := by
    simpa [prefixWord, tailWord_470919, baseEnd_470919] using wordTrace_append hprefix tailTrace_470919
  have hstable : (prefixWord ++ tailWord_470919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470919).length < 2 ^ (prefixWord ++ tailWord_470919).sum := by decide
  have hdescent : baseEnd_470919 < baseStart_470919 := by decide
  rcases family_descends (prefixWord ++ tailWord_470919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470984 : List Nat := [2, 1, 3, 1, 4, 2, 3, 2, 3]
def baseStart_470984 : Nat := 118140960795 + 470984 * 2 ^ 59
def prefixEnd_470984 : Nat := 4983230072969 + 3 ^ 40 * 470984 * 2
def baseEnd_470984 : Nat := 107484965589906891837329

theorem tailTrace_470984 : CollatzResearch.WordTrace tailWord_470984 prefixEnd_470984 107484965589906891837329 := by
  unfold tailWord_470984
  simp only [CollatzResearch.WordTrace]
  refine ⟨8589098862856440254170003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11452131817141920338893337 8589098862856440254170003)
  ·
    refine ⟨12883648294284660381255005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8589098862856440254170003 12883648294284660381255005)
    ·
      refine ⟨4831368110356747642970627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12883648294284660381255005 4831368110356747642970627)
      ·
        refine ⟨7247052165535121464455941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4831368110356747642970627 7247052165535121464455941)
        ·
          refine ⟨1358822281037835274585489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7247052165535121464455941 1358822281037835274585489)
          ·
            refine ⟨1019116710778376455939117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1358822281037835274585489 1019116710778376455939117)
            ·
              refine ⟨382168766541891170977169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1019116710778376455939117 382168766541891170977169)
              ·
                refine ⟨286626574906418378232877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 382168766541891170977169 286626574906418378232877)
                ·
                  refine ⟨107484965589906891837329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 286626574906418378232877 107484965589906891837329)
                  ·
                    rfl

theorem cell21_470984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 2, 3].length) (baseStart_470984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_470984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_470984 prefixEnd_470984 := by exact prefixLift 470984
  have htrace : WordTrace (prefixWord ++ tailWord_470984) baseStart_470984 baseEnd_470984 := by
    simpa [prefixWord, tailWord_470984, baseEnd_470984] using wordTrace_append hprefix tailTrace_470984
  have hstable : (prefixWord ++ tailWord_470984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470984).length < 2 ^ (prefixWord ++ tailWord_470984).sum := by decide
  have hdescent : baseEnd_470984 < baseStart_470984 := by decide
  rcases family_descends (prefixWord ++ tailWord_470984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471009 : List Nat := [1, 2, 3, 1, 2, 1, 2, 4, 5]
def baseStart_471009 : Nat := 118140960795 + 471009 * 2 ^ 59
def prefixEnd_471009 : Nat := 4983230072969 + 3 ^ 40 * 471009 * 2
def baseEnd_471009 : Nat := 107490670930512403920611

theorem tailTrace_471009 : CollatzResearch.WordTrace tailWord_471009 prefixEnd_471009 107490670930512403920611 := by
  unfold tailWord_471009
  simp only [CollatzResearch.WordTrace]
  refine ⟨17179109550622309778000081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11452739700414873185333387 17179109550622309778000081)
  ·
    refine ⟨12884332162966732333500061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17179109550622309778000081 12884332162966732333500061)
    ·
      refine ⟨4831624561112524625062523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12884332162966732333500061 4831624561112524625062523)
      ·
        refine ⟨7247436841668786937593785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4831624561112524625062523 7247436841668786937593785)
        ·
          refine ⟨5435577631251590203195339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7247436841668786937593785 5435577631251590203195339)
          ·
            refine ⟨8153366446877385304793009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5435577631251590203195339 8153366446877385304793009)
            ·
              refine ⟨6115024835158038978594757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8153366446877385304793009 6115024835158038978594757)
              ·
                refine ⟨1146567156592132308486517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6115024835158038978594757 1146567156592132308486517)
                ·
                  refine ⟨107490670930512403920611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1146567156592132308486517 107490670930512403920611)
                  ·
                    rfl

theorem cell21_471009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 5].length) (baseStart_471009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_471009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_471009 prefixEnd_471009 := by exact prefixLift 471009
  have htrace : WordTrace (prefixWord ++ tailWord_471009) baseStart_471009 baseEnd_471009 := by
    simpa [prefixWord, tailWord_471009, baseEnd_471009] using wordTrace_append hprefix tailTrace_471009
  have hstable : (prefixWord ++ tailWord_471009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471009).length < 2 ^ (prefixWord ++ tailWord_471009).sum := by decide
  have hdescent : baseEnd_471009 < baseStart_471009 := by decide
  rcases family_descends (prefixWord ++ tailWord_471009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471060 : List Nat := [2, 4, 3, 2, 1, 1, 1, 2, 5]
def baseStart_471060 : Nat := 118140960795 + 471060 * 2 ^ 59
def prefixEnd_471060 : Nat := 4983230072969 + 3 ^ 40 * 471060 * 2
def baseEnd_471060 : Nat := 107502309825347648570507

theorem tailTrace_471060 : CollatzResearch.WordTrace tailWord_471060 prefixEnd_471060 107502309825347648570507 := by
  unfold tailWord_471060
  simp only [CollatzResearch.WordTrace]
  refine ⟨8590484836718772744053317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11453979782291696992071089 8590484836718772744053317)
  ·
    refine ⟨1610715906884769889509997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8590484836718772744053317 1610715906884769889509997)
    ·
      refine ⟨604018465081788708566249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1610715906884769889509997 604018465081788708566249)
      ·
        refine ⟨453013848811341531424687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 604018465081788708566249 453013848811341531424687)
        ·
          refine ⟨679520773217012297137031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453013848811341531424687 679520773217012297137031)
          ·
            refine ⟨1019281159825518445705547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 679520773217012297137031 1019281159825518445705547)
            ·
              refine ⟨1528921739738277668558321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1019281159825518445705547 1528921739738277668558321)
              ·
                refine ⟨1146691304803708251418741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1528921739738277668558321 1146691304803708251418741)
                ·
                  refine ⟨107502309825347648570507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1146691304803708251418741 107502309825347648570507)
                  ·
                    rfl

theorem cell21_471060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_471060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_471060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_471060 prefixEnd_471060 := by exact prefixLift 471060
  have htrace : WordTrace (prefixWord ++ tailWord_471060) baseStart_471060 baseEnd_471060 := by
    simpa [prefixWord, tailWord_471060, baseEnd_471060] using wordTrace_append hprefix tailTrace_471060
  have hstable : (prefixWord ++ tailWord_471060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471060).length < 2 ^ (prefixWord ++ tailWord_471060).sum := by decide
  have hdescent : baseEnd_471060 < baseStart_471060 := by decide
  rcases family_descends (prefixWord ++ tailWord_471060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471071 : List Nat := [1, 1, 2, 4, 1, 2, 5, 5]
def baseStart_471071 : Nat := 118140960795 + 471071 * 2 ^ 59
def prefixEnd_471071 : Nat := 4983230072969 + 3 ^ 40 * 471071 * 2
def baseEnd_471071 : Nat := 35834940058404691295717

theorem tailTrace_471071 : CollatzResearch.WordTrace tailWord_471071 prefixEnd_471071 35834940058404691295717 := by
  unfold tailWord_471071
  simp only [CollatzResearch.WordTrace]
  refine ⟨17181370876397694366757067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11454247250931796244504711 17181370876397694366757067)
  ·
    refine ⟨25772056314596541550135601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17181370876397694366757067 25772056314596541550135601)
    ·
      refine ⟨19329042235947406162601701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25772056314596541550135601 19329042235947406162601701)
      ·
        refine ⟨3624195419240138655487819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19329042235947406162601701 3624195419240138655487819)
        ·
          refine ⟨5436293128860207983231729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3624195419240138655487819 5436293128860207983231729)
          ·
            refine ⟨4077219846645155987423797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5436293128860207983231729 4077219846645155987423797)
            ·
              refine ⟨382239360622983373820981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4077219846645155987423797 382239360622983373820981)
              ·
                refine ⟨35834940058404691295717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 382239360622983373820981 35834940058404691295717)
                ·
                  rfl

theorem cell21_471071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 5].length) (baseStart_471071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_471071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_471071 prefixEnd_471071 := by exact prefixLift 471071
  have htrace : WordTrace (prefixWord ++ tailWord_471071) baseStart_471071 baseEnd_471071 := by
    simpa [prefixWord, tailWord_471071, baseEnd_471071] using wordTrace_append hprefix tailTrace_471071
  have hstable : (prefixWord ++ tailWord_471071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471071).length < 2 ^ (prefixWord ++ tailWord_471071).sum := by decide
  have hdescent : baseEnd_471071 < baseStart_471071 := by decide
  rcases family_descends (prefixWord ++ tailWord_471071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471099 : List Nat := [1, 1, 1, 1, 1, 2, 1, 7, 6]
def baseStart_471099 : Nat := 118140960795 + 471099 * 2 ^ 59
def prefixEnd_471099 : Nat := 4983230072969 + 3 ^ 40 * 471099 * 2
def baseEnd_471099 : Nat := 107511210156692247420427

theorem tailTrace_471099 : CollatzResearch.WordTrace tailWord_471099 prefixEnd_471099 107511210156692247420427 := by
  unfold tailWord_471099
  simp only [CollatzResearch.WordTrace]
  refine ⟨17182392120296255148776351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11454928080197503432517567 17182392120296255148776351)
  ·
    refine ⟨25773588180444382723164527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17182392120296255148776351 25773588180444382723164527)
    ·
      refine ⟨38660382270666574084746791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25773588180444382723164527 38660382270666574084746791)
      ·
        refine ⟨57990573405999861127120187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38660382270666574084746791 57990573405999861127120187)
        ·
          refine ⟨86985860108999791690680281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57990573405999861127120187 86985860108999791690680281)
          ·
            refine ⟨65239395081749843768010211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86985860108999791690680281 65239395081749843768010211)
            ·
              refine ⟨97859092622624765652015317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65239395081749843768010211 97859092622624765652015317)
              ·
                refine ⟨2293572483342767944969109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 97859092622624765652015317 2293572483342767944969109)
                ·
                  refine ⟨107511210156692247420427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2293572483342767944969109 107511210156692247420427)
                  ·
                    rfl

theorem cell21_471099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 6].length) (baseStart_471099 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_471099 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_471099 prefixEnd_471099 := by exact prefixLift 471099
  have htrace : WordTrace (prefixWord ++ tailWord_471099) baseStart_471099 baseEnd_471099 := by
    simpa [prefixWord, tailWord_471099, baseEnd_471099] using wordTrace_append hprefix tailTrace_471099
  have hstable : (prefixWord ++ tailWord_471099).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471099).length < 2 ^ (prefixWord ++ tailWord_471099).sum := by decide
  have hdescent : baseEnd_471099 < baseStart_471099 := by decide
  rcases family_descends (prefixWord ++ tailWord_471099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471116 : List Nat := [2, 2, 1, 3, 1, 1, 2, 5, 4]
def baseStart_471116 : Nat := 118140960795 + 471116 * 2 ^ 59
def prefixEnd_471116 : Nat := 4983230072969 + 3 ^ 40 * 471116 * 2
def baseEnd_471116 : Nat := 107515089788303995637059

theorem tailTrace_471116 : CollatzResearch.WordTrace tailWord_471116 prefixEnd_471116 107515089788303995637059 := by
  unfold tailWord_471116
  simp only [CollatzResearch.WordTrace]
  refine ⟨8591506080617333526072601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11455341440823111368096801 8591506080617333526072601)
  ·
    refine ⟨6443629560463000144554451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8591506080617333526072601 6443629560463000144554451)
    ·
      refine ⟨9665444340694500216831677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6443629560463000144554451 9665444340694500216831677)
      ·
        refine ⟨3624541627760437581311879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9665444340694500216831677 3624541627760437581311879)
        ·
          refine ⟨5436812441640656371967819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3624541627760437581311879 5436812441640656371967819)
          ·
            refine ⟨8155218662460984557951729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5436812441640656371967819 8155218662460984557951729)
            ·
              refine ⟨6116413996845738418463797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8155218662460984557951729 6116413996845738418463797)
              ·
                refine ⟨573413812204287976730981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6116413996845738418463797 573413812204287976730981)
                ·
                  refine ⟨107515089788303995637059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 573413812204287976730981 107515089788303995637059)
                  ·
                    rfl

theorem cell21_471116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_471116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_471116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_471116 prefixEnd_471116 := by exact prefixLift 471116
  have htrace : WordTrace (prefixWord ++ tailWord_471116) baseStart_471116 baseEnd_471116 := by
    simpa [prefixWord, tailWord_471116, baseEnd_471116] using wordTrace_append hprefix tailTrace_471116
  have hstable : (prefixWord ++ tailWord_471116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471116).length < 2 ^ (prefixWord ++ tailWord_471116).sum := by decide
  have hdescent : baseEnd_471116 < baseStart_471116 := by decide
  rcases family_descends (prefixWord ++ tailWord_471116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471130 : List Nat := [3, 1, 1, 2, 1, 1, 5, 7]
def baseStart_471130 : Nat := 118140960795 + 471130 * 2 ^ 59
def prefixEnd_471130 : Nat := 4983230072969 + 3 ^ 40 * 471130 * 2
def baseEnd_471130 : Nat := 35839428259681027467899

theorem tailTrace_471130 : CollatzResearch.WordTrace tailWord_471130 prefixEnd_471130 35839428259681027467899 := by
  unfold tailWord_471130
  simp only [CollatzResearch.WordTrace]
  refine ⟨4295880695795986860788711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11455681855455964962103229 4295880695795986860788711)
  ·
    refine ⟨6443821043693980291183067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4295880695795986860788711 6443821043693980291183067)
    ·
      refine ⟨9665731565540970436774601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6443821043693980291183067 9665731565540970436774601)
      ·
        refine ⟨7249298674155727827580951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9665731565540970436774601 7249298674155727827580951)
        ·
          refine ⟨10873948011233591741371427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7249298674155727827580951 10873948011233591741371427)
          ·
            refine ⟨16310922016850387612057141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10873948011233591741371427 16310922016850387612057141)
            ·
              refine ⟨1529148939079723838630357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16310922016850387612057141 1529148939079723838630357)
              ·
                refine ⟨35839428259681027467899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1529148939079723838630357 35839428259681027467899)
                ·
                  rfl

theorem cell21_471130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 7].length) (baseStart_471130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_471130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_471130 prefixEnd_471130 := by exact prefixLift 471130
  have htrace : WordTrace (prefixWord ++ tailWord_471130) baseStart_471130 baseEnd_471130 := by
    simpa [prefixWord, tailWord_471130, baseEnd_471130] using wordTrace_append hprefix tailTrace_471130
  have hstable : (prefixWord ++ tailWord_471130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471130).length < 2 ^ (prefixWord ++ tailWord_471130).sum := by decide
  have hdescent : baseEnd_471130 < baseStart_471130 := by decide
  rcases family_descends (prefixWord ++ tailWord_471130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471133 : List Nat := [1, 4, 4, 1, 1, 1, 1, 2, 6]
def baseStart_471133 : Nat := 118140960795 + 471133 * 2 ^ 59
def prefixEnd_471133 : Nat := 4983230072969 + 3 ^ 40 * 471133 * 2
def baseEnd_471133 : Nat := 107518969419915743853691

theorem tailTrace_471133 : CollatzResearch.WordTrace tailWord_471133 prefixEnd_471133 107518969419915743853691 := by
  unfold tailWord_471133
  simp only [CollatzResearch.WordTrace]
  refine ⟨17183632202173078955514053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11455754801448719303676035 17183632202173078955514053)
  ·
    refine ⟨3221931037907452304158885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17183632202173078955514053 3221931037907452304158885)
    ·
      refine ⟨604112069607647307029791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3221931037907452304158885 604112069607647307029791)
      ·
        refine ⟨906168104411470960544687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604112069607647307029791 906168104411470960544687)
        ·
          refine ⟨1359252156617206440817031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 906168104411470960544687 1359252156617206440817031)
          ·
            refine ⟨2038878234925809661225547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1359252156617206440817031 2038878234925809661225547)
            ·
              refine ⟨3058317352388714491838321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2038878234925809661225547 3058317352388714491838321)
              ·
                refine ⟨2293738014291535868878741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3058317352388714491838321 2293738014291535868878741)
                ·
                  refine ⟨107518969419915743853691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2293738014291535868878741 107518969419915743853691)
                  ·
                    rfl

theorem cell21_471133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_471133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_471133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_471133 prefixEnd_471133 := by exact prefixLift 471133
  have htrace : WordTrace (prefixWord ++ tailWord_471133) baseStart_471133 baseEnd_471133 := by
    simpa [prefixWord, tailWord_471133, baseEnd_471133] using wordTrace_append hprefix tailTrace_471133
  have hstable : (prefixWord ++ tailWord_471133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471133).length < 2 ^ (prefixWord ++ tailWord_471133).sum := by decide
  have hdescent : baseEnd_471133 < baseStart_471133 := by decide
  rcases family_descends (prefixWord ++ tailWord_471133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471223 : List Nat := [1, 1, 3, 1, 4, 4, 1, 6]
def baseStart_471223 : Nat := 118140960795 + 471223 * 2 ^ 59
def prefixEnd_471223 : Nat := 4983230072969 + 3 ^ 40 * 471223 * 2
def baseEnd_471223 : Nat := 35846502882031862451169

theorem tailTrace_471223 : CollatzResearch.WordTrace tailWord_471223 prefixEnd_471223 35846502882031862451169 := by
  unfold tailWord_471223
  simp only [CollatzResearch.WordTrace]
  refine ⟨17186914771847024326290323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11457943181231349550860215 17186914771847024326290323)
  ·
    refine ⟨25780372157770536489435485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17186914771847024326290323 25780372157770536489435485)
    ·
      refine ⟨9667639559163951183538307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25780372157770536489435485 9667639559163951183538307)
      ·
        refine ⟨14501459338745926775307461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9667639559163951183538307 14501459338745926775307461)
        ·
          refine ⟨2719023626014861270370149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14501459338745926775307461 2719023626014861270370149)
          ·
            refine ⟨509816929877786488194403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2719023626014861270370149 509816929877786488194403)
            ·
              refine ⟨764725394816679732291605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 509816929877786488194403 764725394816679732291605)
              ·
                refine ⟨35846502882031862451169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 764725394816679732291605 35846502882031862451169)
                ·
                  rfl

theorem cell21_471223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 6].length) (baseStart_471223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_471223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_471223 prefixEnd_471223 := by exact prefixLift 471223
  have htrace : WordTrace (prefixWord ++ tailWord_471223) baseStart_471223 baseEnd_471223 := by
    simpa [prefixWord, tailWord_471223, baseEnd_471223] using wordTrace_append hprefix tailTrace_471223
  have hstable : (prefixWord ++ tailWord_471223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471223).length < 2 ^ (prefixWord ++ tailWord_471223).sum := by decide
  have hdescent : baseEnd_471223 < baseStart_471223 := by decide
  rcases family_descends (prefixWord ++ tailWord_471223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471260 : List Nat := [2, 2, 5, 2, 2, 1, 1, 2, 4]
def baseStart_471260 : Nat := 118140960795 + 471260 * 2 ^ 59
def prefixEnd_471260 : Nat := 4983230072969 + 3 ^ 40 * 471260 * 2
def baseEnd_471260 : Nat := 107547952550191745236765

theorem tailTrace_471260 : CollatzResearch.WordTrace tailWord_471260 prefixEnd_471260 107547952550191745236765 := by
  unfold tailWord_471260
  simp only [CollatzResearch.WordTrace]
  refine ⟨8594132136356489822693617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11458842848475319763591489 8594132136356489822693617)
  ·
    refine ⟨6445599102267367367020213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8594132136356489822693617 6445599102267367367020213)
    ·
      refine ⟨604274915837565690658145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6445599102267367367020213 604274915837565690658145)
      ·
        refine ⟨453206186878174267993609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 604274915837565690658145 453206186878174267993609)
        ·
          refine ⟨339904640158630700995207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453206186878174267993609 339904640158630700995207)
          ·
            refine ⟨509856960237946051492811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339904640158630700995207 509856960237946051492811)
            ·
              refine ⟨764785440356919077239217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 509856960237946051492811 764785440356919077239217)
              ·
                refine ⟨573589080267689307929413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 764785440356919077239217 573589080267689307929413)
                ·
                  refine ⟨107547952550191745236765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 573589080267689307929413 107547952550191745236765)
                  ·
                    rfl

theorem cell21_471260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 4].length) (baseStart_471260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_471260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_471260 prefixEnd_471260 := by exact prefixLift 471260
  have htrace : WordTrace (prefixWord ++ tailWord_471260) baseStart_471260 baseEnd_471260 := by
    simpa [prefixWord, tailWord_471260, baseEnd_471260] using wordTrace_append hprefix tailTrace_471260
  have hstable : (prefixWord ++ tailWord_471260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471260).length < 2 ^ (prefixWord ++ tailWord_471260).sum := by decide
  have hdescent : baseEnd_471260 < baseStart_471260 := by decide
  rcases family_descends (prefixWord ++ tailWord_471260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471271 : List Nat := [1, 1, 5, 3, 1, 1, 2, 4, 3]
def baseStart_471271 : Nat := 118140960795 + 471271 * 2 ^ 59
def prefixEnd_471271 : Nat := 4983230072969 + 3 ^ 40 * 471271 * 2
def baseEnd_471271 : Nat := 107550462900058170553409

theorem tailTrace_471271 : CollatzResearch.WordTrace tailWord_471271 prefixEnd_471271 107550462900058170553409 := by
  unfold tailWord_471271
  simp only [CollatzResearch.WordTrace]
  refine ⟨17188665475673128524037667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11459110317115419016025111 17188665475673128524037667)
  ·
    refine ⟨25782998213509692786056501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17188665475673128524037667 25782998213509692786056501)
    ·
      refine ⟨2417156082516533698692797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25782998213509692786056501 2417156082516533698692797)
      ·
        refine ⟨906433530943700137009799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2417156082516533698692797 906433530943700137009799)
        ·
          refine ⟨1359650296415550205514699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 906433530943700137009799 1359650296415550205514699)
          ·
            refine ⟨2039475444623325308272049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1359650296415550205514699 2039475444623325308272049)
            ·
              refine ⟨1529606583467493981204037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2039475444623325308272049 1529606583467493981204037)
              ·
                refine ⟨286801234400155121475757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1529606583467493981204037 286801234400155121475757)
                ·
                  refine ⟨107550462900058170553409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 286801234400155121475757 107550462900058170553409)
                  ·
                    rfl

theorem cell21_471271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 4, 3].length) (baseStart_471271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_471271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_471271 prefixEnd_471271 := by exact prefixLift 471271
  have htrace : WordTrace (prefixWord ++ tailWord_471271) baseStart_471271 baseEnd_471271 := by
    simpa [prefixWord, tailWord_471271, baseEnd_471271] using wordTrace_append hprefix tailTrace_471271
  have hstable : (prefixWord ++ tailWord_471271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471271).length < 2 ^ (prefixWord ++ tailWord_471271).sum := by decide
  have hdescent : baseEnd_471271 < baseStart_471271 := by decide
  rcases family_descends (prefixWord ++ tailWord_471271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471330 : List Nat := [3, 3, 1, 1, 3, 1, 3, 1, 5]
def baseStart_471330 : Nat := 118140960795 + 471330 * 2 ^ 59
def prefixEnd_471330 : Nat := 4983230072969 + 3 ^ 40 * 471330 * 2
def baseEnd_471330 : Nat := 107563927503887179069955

theorem tailTrace_471330 : CollatzResearch.WordTrace tailWord_471330 prefixEnd_471330 107563927503887179069955 := by
  unfold tailWord_471330
  simp only [CollatzResearch.WordTrace]
  refine ⟨4297704345614845400108861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11460544921639587733623629 4297704345614845400108861)
  ·
    refine ⟨1611639129605567025040823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4297704345614845400108861 1611639129605567025040823)
    ·
      refine ⟨2417458694408350537561235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1611639129605567025040823 2417458694408350537561235)
      ·
        refine ⟨3626188041612525806341853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2417458694408350537561235 3626188041612525806341853)
        ·
          refine ⟨1359820515604697177378195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3626188041612525806341853 1359820515604697177378195)
          ·
            refine ⟨2039730773407045766067293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1359820515604697177378195 2039730773407045766067293)
            ·
              refine ⟨764899040027642162275235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2039730773407045766067293 764899040027642162275235)
              ·
                refine ⟨1147348560041463243412853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 764899040027642162275235 1147348560041463243412853)
                ·
                  refine ⟨107563927503887179069955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1147348560041463243412853 107563927503887179069955)
                  ·
                    rfl

theorem cell21_471330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_471330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_471330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_471330 prefixEnd_471330 := by exact prefixLift 471330
  have htrace : WordTrace (prefixWord ++ tailWord_471330) baseStart_471330 baseEnd_471330 := by
    simpa [prefixWord, tailWord_471330, baseEnd_471330] using wordTrace_append hprefix tailTrace_471330
  have hstable : (prefixWord ++ tailWord_471330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471330).length < 2 ^ (prefixWord ++ tailWord_471330).sum := by decide
  have hdescent : baseEnd_471330 < baseStart_471330 := by decide
  rcases family_descends (prefixWord ++ tailWord_471330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471381 : List Nat := [1, 3, 2, 2, 5, 1, 2, 2, 3]
def baseStart_471381 : Nat := 118140960795 + 471381 * 2 ^ 59
def prefixEnd_471381 : Nat := 4983230072969 + 3 ^ 40 * 471381 * 2
def baseEnd_471381 : Nat := 107575566398722423719851

theorem tailTrace_471381 : CollatzResearch.WordTrace tailWord_471381 prefixEnd_471381 107575566398722423719851 := by
  unfold tailWord_471381
  simp only [CollatzResearch.WordTrace]
  refine ⟨17192677505274617310541997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11461785003516411540361331 17192677505274617310541997)
  ·
    refine ⟨6447254064477981491453249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17192677505274617310541997 6447254064477981491453249)
    ·
      refine ⟨4835440548358486118589937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6447254064477981491453249 4835440548358486118589937)
      ·
        refine ⟨3626580411268864588942453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4835440548358486118589937 3626580411268864588942453)
        ·
          refine ⟨339991913556456055213355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3626580411268864588942453 339991913556456055213355)
          ·
            refine ⟨509987870334684082820033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339991913556456055213355 509987870334684082820033)
            ·
              refine ⟨382490902751013062115025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 509987870334684082820033 382490902751013062115025)
              ·
                refine ⟨286868177063259796586269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 382490902751013062115025 286868177063259796586269)
                ·
                  refine ⟨107575566398722423719851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 286868177063259796586269 107575566398722423719851)
                  ·
                    rfl

theorem cell21_471381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 2, 3].length) (baseStart_471381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_471381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_471381 prefixEnd_471381 := by exact prefixLift 471381
  have htrace : WordTrace (prefixWord ++ tailWord_471381) baseStart_471381 baseEnd_471381 := by
    simpa [prefixWord, tailWord_471381, baseEnd_471381] using wordTrace_append hprefix tailTrace_471381
  have hstable : (prefixWord ++ tailWord_471381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471381).length < 2 ^ (prefixWord ++ tailWord_471381).sum := by decide
  have hdescent : baseEnd_471381 < baseStart_471381 := by decide
  rcases family_descends (prefixWord ++ tailWord_471381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471392 : List Nat := [2, 1, 1, 3, 6, 1, 1, 6]
def baseStart_471392 : Nat := 118140960795 + 471392 * 2 ^ 59
def prefixEnd_471392 : Nat := 4983230072969 + 3 ^ 40 * 471392 * 2
def baseEnd_471392 : Nat := 35859358916196283012165

theorem tailTrace_471392 : CollatzResearch.WordTrace tailWord_471392 prefixEnd_471392 35859358916196283012165 := by
  unfold tailWord_471392
  simp only [CollatzResearch.WordTrace]
  refine ⟨8596539354117383094596215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11462052472156510792794953 8596539354117383094596215)
  ·
    refine ⟨12894809031176074641894323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8596539354117383094596215 12894809031176074641894323)
    ·
      refine ⟨19342213546764111962841485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12894809031176074641894323 19342213546764111962841485)
      ·
        refine ⟨7253330080036541986065557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19342213546764111962841485 7253330080036541986065557)
        ·
          refine ⟨339999847501712905596823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7253330080036541986065557 339999847501712905596823)
          ·
            refine ⟨509999771252569358395235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339999847501712905596823 509999771252569358395235)
            ·
              refine ⟨764999656878854037592853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 509999771252569358395235 764999656878854037592853)
              ·
                refine ⟨35859358916196283012165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 764999656878854037592853 35859358916196283012165)
                ·
                  rfl

theorem cell21_471392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 6].length) (baseStart_471392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_471392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_471392 prefixEnd_471392 := by exact prefixLift 471392
  have htrace : WordTrace (prefixWord ++ tailWord_471392) baseStart_471392 baseEnd_471392 := by
    simpa [prefixWord, tailWord_471392, baseEnd_471392] using wordTrace_append hprefix tailTrace_471392
  have hstable : (prefixWord ++ tailWord_471392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471392).length < 2 ^ (prefixWord ++ tailWord_471392).sum := by decide
  have hdescent : baseEnd_471392 < baseStart_471392 := by decide
  rcases family_descends (prefixWord ++ tailWord_471392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471479 : List Nat := [1, 1, 3, 1, 3, 3, 1, 2, 6]
def baseStart_471479 : Nat := 118140960795 + 471479 * 2 ^ 59
def prefixEnd_471479 : Nat := 4983230072969 + 3 ^ 40 * 471479 * 2
def baseEnd_471479 : Nat := 107597931333896031086317

theorem tailTrace_471479 : CollatzResearch.WordTrace tailWord_471479 prefixEnd_471479 107597931333896031086317 := by
  unfold tailWord_471479
  simp only [CollatzResearch.WordTrace]
  refine ⟨17196251858919580047609491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11464167905946386698406327 17196251858919580047609491)
  ·
    refine ⟨25794377788379370071414237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17196251858919580047609491 25794377788379370071414237)
    ·
      refine ⟨9672891670642263776780339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25794377788379370071414237 9672891670642263776780339)
      ·
        refine ⟨14509337505963395665170509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9672891670642263776780339 14509337505963395665170509)
        ·
          refine ⟨5441001564736273374438941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14509337505963395665170509 5441001564736273374438941)
          ·
            refine ⟨2040375586776102515414603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5441001564736273374438941 2040375586776102515414603)
            ·
              refine ⟨3060563380164153773121905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2040375586776102515414603 3060563380164153773121905)
              ·
                refine ⟨2295422535123115329841429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3060563380164153773121905 2295422535123115329841429)
                ·
                  refine ⟨107597931333896031086317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2295422535123115329841429 107597931333896031086317)
                  ·
                    rfl

theorem cell21_471479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 6].length) (baseStart_471479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_471479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_471479 prefixEnd_471479 := by exact prefixLift 471479
  have htrace : WordTrace (prefixWord ++ tailWord_471479) baseStart_471479 baseEnd_471479 := by
    simpa [prefixWord, tailWord_471479, baseEnd_471479] using wordTrace_append hprefix tailTrace_471479
  have hstable : (prefixWord ++ tailWord_471479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471479).length < 2 ^ (prefixWord ++ tailWord_471479).sum := by decide
  have hdescent : baseEnd_471479 < baseStart_471479 := by decide
  rcases family_descends (prefixWord ++ tailWord_471479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471569 : List Nat := [1, 2, 2, 1, 1, 2, 2, 10]
def baseStart_471569 : Nat := 118140960795 + 471569 * 2 ^ 59
def prefixEnd_471569 : Nat := 4983230072969 + 3 ^ 40 * 471569 * 2
def baseEnd_471569 : Nat := 35872823520025291528711

theorem tailTrace_471569 : CollatzResearch.WordTrace tailWord_471569 prefixEnd_471569 35872823520025291528711 := by
  unfold tailWord_471569
  simp only [CollatzResearch.WordTrace]
  refine ⟨17199534428593525418385761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11466356285729016945590507 17199534428593525418385761)
  ·
    refine ⟨12899650821445144063789321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17199534428593525418385761 12899650821445144063789321)
    ·
      refine ⟨9674738116083858047841991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12899650821445144063789321 9674738116083858047841991)
      ·
        refine ⟨14512107174125787071762987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9674738116083858047841991 14512107174125787071762987)
        ·
          refine ⟨21768160761188680607644481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14512107174125787071762987 21768160761188680607644481)
          ·
            refine ⟨16326120570891510455733361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21768160761188680607644481 16326120570891510455733361)
            ·
              refine ⟨12244590428168632841800021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16326120570891510455733361 12244590428168632841800021)
              ·
                refine ⟨35872823520025291528711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12244590428168632841800021 35872823520025291528711)
                ·
                  rfl

theorem cell21_471569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 10].length) (baseStart_471569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_471569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_471569 prefixEnd_471569 := by exact prefixLift 471569
  have htrace : WordTrace (prefixWord ++ tailWord_471569) baseStart_471569 baseEnd_471569 := by
    simpa [prefixWord, tailWord_471569, baseEnd_471569] using wordTrace_append hprefix tailTrace_471569
  have hstable : (prefixWord ++ tailWord_471569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471569).length < 2 ^ (prefixWord ++ tailWord_471569).sum := by decide
  have hdescent : baseEnd_471569 < baseStart_471569 := by decide
  rcases family_descends (prefixWord ++ tailWord_471569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471606 : List Nat := [5, 1, 2, 1, 2, 3, 1, 2, 4]
def baseStart_471606 : Nat := 118140960795 + 471606 * 2 ^ 59
def prefixEnd_471606 : Nat := 4983230072969 + 3 ^ 40 * 471606 * 2
def baseEnd_471606 : Nat := 107626914464172032469391

theorem tailTrace_471606 : CollatzResearch.WordTrace tailWord_471606 prefixEnd_471606 107626914464172032469391 := by
  unfold tailWord_471606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1075055245591217546092667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11467255952972987158321781 1075055245591217546092667)
  ·
    refine ⟨1612582868386826319139001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1075055245591217546092667 1612582868386826319139001)
    ·
      refine ⟨1209437151290119739354251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1612582868386826319139001 1209437151290119739354251)
      ·
        refine ⟨1814155726935179609031377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1209437151290119739354251 1814155726935179609031377)
        ·
          refine ⟨1360616795201384706773533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1814155726935179609031377 1360616795201384706773533)
          ·
            refine ⟨510231298200519265040075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1360616795201384706773533 510231298200519265040075)
            ·
              refine ⟨765346947300778897560113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510231298200519265040075 765346947300778897560113)
              ·
                refine ⟨574010210475584173170085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 765346947300778897560113 574010210475584173170085)
                ·
                  refine ⟨107626914464172032469391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 574010210475584173170085 107626914464172032469391)
                  ·
                    rfl

theorem cell21_471606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_471606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_471606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_471606 prefixEnd_471606 := by exact prefixLift 471606
  have htrace : WordTrace (prefixWord ++ tailWord_471606) baseStart_471606 baseEnd_471606 := by
    simpa [prefixWord, tailWord_471606, baseEnd_471606] using wordTrace_append hprefix tailTrace_471606
  have hstable : (prefixWord ++ tailWord_471606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471606).length < 2 ^ (prefixWord ++ tailWord_471606).sum := by decide
  have hdescent : baseEnd_471606 < baseStart_471606 := by decide
  rcases family_descends (prefixWord ++ tailWord_471606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471617 : List Nat := [1, 2, 5, 1, 1, 2, 1, 3, 5]
def baseStart_471617 : Nat := 118140960795 + 471617 * 2 ^ 59
def prefixEnd_471617 : Nat := 4983230072969 + 3 ^ 40 * 471617 * 2
def baseEnd_471617 : Nat := 107629424814038457786035

theorem tailTrace_471617 : CollatzResearch.WordTrace tailWord_471617 prefixEnd_471617 107629424814038457786035 := by
  unfold tailWord_471617
  simp only [CollatzResearch.WordTrace]
  refine ⟨17201285132419629616133105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11467523421613086410755403 17201285132419629616133105)
  ·
    refine ⟨12900963849314722212099829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17201285132419629616133105 12900963849314722212099829)
    ·
      refine ⟨1209465360873255207384359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12900963849314722212099829 1209465360873255207384359)
      ·
        refine ⟨1814198041309882811076539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1209465360873255207384359 1814198041309882811076539)
        ·
          refine ⟨2721297061964824216614809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1814198041309882811076539 2721297061964824216614809)
          ·
            refine ⟨2040972796473618162461107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2721297061964824216614809 2040972796473618162461107)
            ·
              refine ⟨3061459194710427243691661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2040972796473618162461107 3061459194710427243691661)
              ·
                refine ⟨1148047198016410216384373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3061459194710427243691661 1148047198016410216384373)
                ·
                  refine ⟨107629424814038457786035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1148047198016410216384373 107629424814038457786035)
                  ·
                    rfl

theorem cell21_471617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 5].length) (baseStart_471617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_471617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_471617 prefixEnd_471617 := by exact prefixLift 471617
  have htrace : WordTrace (prefixWord ++ tailWord_471617) baseStart_471617 baseEnd_471617 := by
    simpa [prefixWord, tailWord_471617, baseEnd_471617] using wordTrace_append hprefix tailTrace_471617
  have hstable : (prefixWord ++ tailWord_471617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471617).length < 2 ^ (prefixWord ++ tailWord_471617).sum := by decide
  have hdescent : baseEnd_471617 < baseStart_471617 := by decide
  rcases family_descends (prefixWord ++ tailWord_471617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471631 : List Nat := [1, 1, 2, 1, 1, 2, 4, 5, 4]
def baseStart_471631 : Nat := 118140960795 + 471631 * 2 ^ 59
def prefixEnd_471631 : Nat := 4983230072969 + 3 ^ 40 * 471631 * 2
def baseEnd_471631 : Nat := 107632619804777544552673

theorem tailTrace_471631 : CollatzResearch.WordTrace tailWord_471631 prefixEnd_471631 107632619804777544552673 := by
  unfold tailWord_471631
  simp only [CollatzResearch.WordTrace]
  refine ⟨17201795754368910007142747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11467863836245940004761831 17201795754368910007142747)
  ·
    refine ⟨25802693631553365010714121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17201795754368910007142747 25802693631553365010714121)
    ·
      refine ⟨19352020223665023758035591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25802693631553365010714121 19352020223665023758035591)
      ·
        refine ⟨29028030335497535637053387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19352020223665023758035591 29028030335497535637053387)
        ·
          refine ⟨43542045503246303455580081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29028030335497535637053387 43542045503246303455580081)
          ·
            refine ⟨32656534127434727591685061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43542045503246303455580081 32656534127434727591685061)
            ·
              refine ⟨6123100148894011423440949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32656534127434727591685061 6123100148894011423440949)
              ·
                refine ⟨574040638958813570947589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6123100148894011423440949 574040638958813570947589)
                ·
                  refine ⟨107632619804777544552673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 574040638958813570947589 107632619804777544552673)
                  ·
                    rfl

theorem cell21_471631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 4].length) (baseStart_471631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_471631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_471631 prefixEnd_471631 := by exact prefixLift 471631
  have htrace : WordTrace (prefixWord ++ tailWord_471631) baseStart_471631 baseEnd_471631 := by
    simpa [prefixWord, tailWord_471631, baseEnd_471631] using wordTrace_append hprefix tailTrace_471631
  have hstable : (prefixWord ++ tailWord_471631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471631).length < 2 ^ (prefixWord ++ tailWord_471631).sum := by decide
  have hdescent : baseEnd_471631 < baseStart_471631 := by decide
  rcases family_descends (prefixWord ++ tailWord_471631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471662 : List Nat := [4, 1, 2, 2, 2, 1, 9]
def baseStart_471662 : Nat := 118140960795 + 471662 * 2 ^ 59
def prefixEnd_471662 : Nat := 4983230072969 + 3 ^ 40 * 471662 * 2
def baseEnd_471662 : Nat := 11959966047458708837327

theorem tailTrace_471662 : CollatzResearch.WordTrace tailWord_471662 prefixEnd_471662 11959966047458708837327 := by
  unfold tailWord_471662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2150365802157075287690155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11468617611504401534347493 2150365802157075287690155)
  ·
    refine ⟨3225548703235612931535233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2150365802157075287690155 3225548703235612931535233)
    ·
      refine ⟨2419161527426709698651425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3225548703235612931535233 2419161527426709698651425)
      ·
        refine ⟨1814371145570032273988569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2419161527426709698651425 1814371145570032273988569)
        ·
          refine ⟨1360778359177524205491427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1814371145570032273988569 1360778359177524205491427)
          ·
            refine ⟨2041167538766286308237141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1360778359177524205491427 2041167538766286308237141)
            ·
              refine ⟨11959966047458708837327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2041167538766286308237141 11959966047458708837327)
              ·
                rfl

theorem cell21_471662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 9].length) (baseStart_471662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_471662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_471662 prefixEnd_471662 := by exact prefixLift 471662
  have htrace : WordTrace (prefixWord ++ tailWord_471662) baseStart_471662 baseEnd_471662 := by
    simpa [prefixWord, tailWord_471662, baseEnd_471662] using wordTrace_append hprefix tailTrace_471662
  have hstable : (prefixWord ++ tailWord_471662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471662).length < 2 ^ (prefixWord ++ tailWord_471662).sum := by decide
  have hdescent : baseEnd_471662 < baseStart_471662 := by decide
  rcases family_descends (prefixWord ++ tailWord_471662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471727 : List Nat := [1, 1, 2, 1, 2, 7, 2, 2, 3]
def baseStart_471727 : Nat := 118140960795 + 471727 * 2 ^ 59
def prefixEnd_471727 : Nat := 4983230072969 + 3 ^ 40 * 471727 * 2
def baseEnd_471727 : Nat := 107654528312702710952477

theorem tailTrace_471727 : CollatzResearch.WordTrace tailWord_471727 prefixEnd_471727 107654528312702710952477 := by
  unfold tailWord_471727
  simp only [CollatzResearch.WordTrace]
  refine ⟨17205297162021118402637435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11470198108014078935091623 17205297162021118402637435)
  ·
    refine ⟨25807945743031677603956153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17205297162021118402637435 25807945743031677603956153)
    ·
      refine ⟨19355959307273758202967115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25807945743031677603956153 19355959307273758202967115)
      ·
        refine ⟨29033938960910637304450673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19355959307273758202967115 29033938960910637304450673)
        ·
          refine ⟨21775454220682977978338005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29033938960910637304450673 21775454220682977978338005)
          ·
            refine ⟨510362208297257296367297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 21775454220682977978338005 510362208297257296367297)
            ·
              refine ⟨382771656222942972275473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 510362208297257296367297 382771656222942972275473)
              ·
                refine ⟨287078742167207229206605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 382771656222942972275473 287078742167207229206605)
                ·
                  refine ⟨107654528312702710952477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 287078742167207229206605 107654528312702710952477)
                  ·
                    rfl

theorem cell21_471727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 2, 3].length) (baseStart_471727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_471727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_471727 prefixEnd_471727 := by exact prefixLift 471727
  have htrace : WordTrace (prefixWord ++ tailWord_471727) baseStart_471727 baseEnd_471727 := by
    simpa [prefixWord, tailWord_471727, baseEnd_471727] using wordTrace_append hprefix tailTrace_471727
  have hstable : (prefixWord ++ tailWord_471727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471727).length < 2 ^ (prefixWord ++ tailWord_471727).sum := by decide
  have hdescent : baseEnd_471727 < baseStart_471727 := by decide
  rcases family_descends (prefixWord ++ tailWord_471727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471752 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 7]
def baseStart_471752 : Nat := 118140960795 + 471752 * 2 ^ 59
def prefixEnd_471752 : Nat := 4983230072969 + 3 ^ 40 * 471752 * 2
def baseEnd_471752 : Nat := 107660233653308223035759

theorem tailTrace_471752 : CollatzResearch.WordTrace tailWord_471752 prefixEnd_471752 107660233653308223035759 := by
  unfold tailWord_471752
  simp only [CollatzResearch.WordTrace]
  refine ⟨8603104493465273836148755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11470805991287031781531673 8603104493465273836148755)
  ·
    refine ⟨12904656740197910754223133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8603104493465273836148755 12904656740197910754223133)
    ·
      refine ⟨4839246277574216532833675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12904656740197910754223133 4839246277574216532833675)
      ·
        refine ⟨7258869416361324799250513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4839246277574216532833675 7258869416361324799250513)
        ·
          refine ⟨5444152062270993599437885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7258869416361324799250513 5444152062270993599437885)
          ·
            refine ⟨2041557023351622599789207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5444152062270993599437885 2041557023351622599789207)
            ·
              refine ⟨3062335535027433899683811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2041557023351622599789207 3062335535027433899683811)
              ·
                refine ⟨4593503302541150849525717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3062335535027433899683811 4593503302541150849525717)
                ·
                  refine ⟨107660233653308223035759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4593503302541150849525717 107660233653308223035759)
                  ·
                    rfl

theorem cell21_471752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 7].length) (baseStart_471752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_471752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_471752 prefixEnd_471752 := by exact prefixLift 471752
  have htrace : WordTrace (prefixWord ++ tailWord_471752) baseStart_471752 baseEnd_471752 := by
    simpa [prefixWord, tailWord_471752, baseEnd_471752] using wordTrace_append hprefix tailTrace_471752
  have hstable : (prefixWord ++ tailWord_471752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471752).length < 2 ^ (prefixWord ++ tailWord_471752).sum := by decide
  have hdescent : baseEnd_471752 < baseStart_471752 := by decide
  rcases family_descends (prefixWord ++ tailWord_471752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471800 : List Nat := [2, 1, 2, 1, 1, 2, 7, 1, 4]
def baseStart_471800 : Nat := 118140960795 + 471800 * 2 ^ 59
def prefixEnd_471800 : Nat := 4983230072969 + 3 ^ 40 * 471800 * 2
def baseEnd_471800 : Nat := 107671187907270806235661

theorem tailTrace_471800 : CollatzResearch.WordTrace tailWord_471800 prefixEnd_471800 107671187907270806235661 := by
  unfold tailWord_471800
  simp only [CollatzResearch.WordTrace]
  refine ⟨8603979845378325935022427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11471973127171101246696569 8603979845378325935022427)
  ·
    refine ⟨12905969768067488902533641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8603979845378325935022427 12905969768067488902533641)
    ·
      refine ⟨9679477326050616676900231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12905969768067488902533641 9679477326050616676900231)
      ·
        refine ⟨14519215989075925015350347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9679477326050616676900231 14519215989075925015350347)
        ·
          refine ⟨21778823983613887523025521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14519215989075925015350347 21778823983613887523025521)
          ·
            refine ⟨16334117987710415642269141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21778823983613887523025521 16334117987710415642269141)
            ·
              refine ⟨382830890336962866615683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 16334117987710415642269141 382830890336962866615683)
              ·
                refine ⟨574246335505444299923525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382830890336962866615683 574246335505444299923525)
                ·
                  refine ⟨107671187907270806235661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 574246335505444299923525 107671187907270806235661)
                  ·
                    rfl

theorem cell21_471800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 4].length) (baseStart_471800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_471800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_471800 prefixEnd_471800 := by exact prefixLift 471800
  have htrace : WordTrace (prefixWord ++ tailWord_471800) baseStart_471800 baseEnd_471800 := by
    simpa [prefixWord, tailWord_471800, baseEnd_471800] using wordTrace_append hprefix tailTrace_471800
  have hstable : (prefixWord ++ tailWord_471800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471800).length < 2 ^ (prefixWord ++ tailWord_471800).sum := by decide
  have hdescent : baseEnd_471800 < baseStart_471800 := by decide
  rcases family_descends (prefixWord ++ tailWord_471800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471831 : List Nat := [1, 1, 3, 4, 4, 1, 7]
def baseStart_471831 : Nat := 118140960795 + 471831 * 2 ^ 59
def prefixEnd_471831 : Nat := 4983230072969 + 3 ^ 40 * 471831 * 2
def baseEnd_471831 : Nat := 11964251392180182357659

theorem tailTrace_471831 : CollatzResearch.WordTrace tailWord_471831 prefixEnd_471831 11964251392180182357659 := by
  unfold tailWord_471831
  simp only [CollatzResearch.WordTrace]
  refine ⟨17209090353644344164423347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11472726902429562776282231 17209090353644344164423347)
  ·
    refine ⟨25813635530466516246635021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17209090353644344164423347 25813635530466516246635021)
    ·
      refine ⟨9680113323924943592488133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25813635530466516246635021 9680113323924943592488133)
      ·
        refine ⟨1815021248235926923591525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9680113323924943592488133 1815021248235926923591525)
        ·
          refine ⟨340316484044236298173411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1815021248235926923591525 340316484044236298173411)
          ·
            refine ⟨510474726066354447260117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340316484044236298173411 510474726066354447260117)
            ·
              refine ⟨11964251392180182357659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 510474726066354447260117 11964251392180182357659)
              ·
                rfl

theorem cell21_471831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 7].length) (baseStart_471831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_471831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_471831 prefixEnd_471831 := by exact prefixLift 471831
  have htrace : WordTrace (prefixWord ++ tailWord_471831) baseStart_471831 baseEnd_471831 := by
    simpa [prefixWord, tailWord_471831, baseEnd_471831] using wordTrace_append hprefix tailTrace_471831
  have hstable : (prefixWord ++ tailWord_471831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471831).length < 2 ^ (prefixWord ++ tailWord_471831).sum := by decide
  have hdescent : baseEnd_471831 < baseStart_471831 := by decide
  rcases family_descends (prefixWord ++ tailWord_471831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471904 : List Nat := [2, 1, 1, 3, 3, 1, 2, 3, 5]
def baseStart_471904 : Nat := 118140960795 + 471904 * 2 ^ 59
def prefixEnd_471904 : Nat := 4983230072969 + 3 ^ 40 * 471904 * 2
def baseEnd_471904 : Nat := 107694922124189736502115

theorem tailTrace_471904 : CollatzResearch.WordTrace tailWord_471904 prefixEnd_471904 107694922124189736502115 := by
  unfold tailWord_471904
  simp only [CollatzResearch.WordTrace]
  refine ⟨8605876441189938815915383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11474501921586585087887177 8605876441189938815915383)
  ·
    refine ⟨12908814661784908223873075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8605876441189938815915383 12908814661784908223873075)
    ·
      refine ⟨19363221992677362335809613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12908814661784908223873075 19363221992677362335809613)
      ·
        refine ⟨7261208247254010875928605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19363221992677362335809613 7261208247254010875928605)
        ·
          refine ⟨2722953092720254078473227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7261208247254010875928605 2722953092720254078473227)
          ·
            refine ⟨4084429639080381117709841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2722953092720254078473227 4084429639080381117709841)
            ·
              refine ⟨3063322229310285838282381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4084429639080381117709841 3063322229310285838282381)
              ·
                refine ⟨1148745835991357189355893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3063322229310285838282381 1148745835991357189355893)
                ·
                  refine ⟨107694922124189736502115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1148745835991357189355893 107694922124189736502115)
                  ·
                    rfl

theorem cell21_471904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 5].length) (baseStart_471904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_471904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_471904 prefixEnd_471904 := by exact prefixLift 471904
  have htrace : WordTrace (prefixWord ++ tailWord_471904) baseStart_471904 baseEnd_471904 := by
    simpa [prefixWord, tailWord_471904, baseEnd_471904] using wordTrace_append hprefix tailTrace_471904
  have hstable : (prefixWord ++ tailWord_471904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471904).length < 2 ^ (prefixWord ++ tailWord_471904).sum := by decide
  have hdescent : baseEnd_471904 < baseStart_471904 := by decide
  rcases family_descends (prefixWord ++ tailWord_471904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471969 : List Nat := [1, 2, 3, 4, 1, 2, 3, 1, 4]
def baseStart_471969 : Nat := 118140960795 + 471969 * 2 ^ 59
def prefixEnd_471969 : Nat := 4983230072969 + 3 ^ 40 * 471969 * 2
def baseEnd_471969 : Nat := 107709756009764067918649

theorem tailTrace_471969 : CollatzResearch.WordTrace tailWord_471969 prefixEnd_471969 107709756009764067918649 := by
  unfold tailWord_471969
  simp only [CollatzResearch.WordTrace]
  refine ⟨17214123627144393732946961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11476082418096262488631307 17214123627144393732946961)
  ·
    refine ⟨12910592720358295299710221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17214123627144393732946961 12910592720358295299710221)
    ·
      refine ⟨4841472270134360737391333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12910592720358295299710221 4841472270134360737391333)
      ·
        refine ⟨907776050650192638260875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4841472270134360737391333 907776050650192638260875)
        ·
          refine ⟨1361664075975288957391313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 907776050650192638260875 1361664075975288957391313)
          ·
            refine ⟨1021248056981466718043485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1361664075975288957391313 1021248056981466718043485)
            ·
              refine ⟨382968021368050019266307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1021248056981466718043485 382968021368050019266307)
              ·
                refine ⟨574452032052075028899461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382968021368050019266307 574452032052075028899461)
                ·
                  refine ⟨107709756009764067918649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 574452032052075028899461 107709756009764067918649)
                  ·
                    rfl

theorem cell21_471969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 4].length) (baseStart_471969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_471969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_471969 prefixEnd_471969 := by exact prefixLift 471969
  have htrace : WordTrace (prefixWord ++ tailWord_471969) baseStart_471969 baseEnd_471969 := by
    simpa [prefixWord, tailWord_471969, baseEnd_471969] using wordTrace_append hprefix tailTrace_471969
  have hstable : (prefixWord ++ tailWord_471969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471969).length < 2 ^ (prefixWord ++ tailWord_471969).sum := by decide
  have hdescent : baseEnd_471969 < baseStart_471969 := by decide
  rcases family_descends (prefixWord ++ tailWord_471969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471994 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 8]
def baseStart_471994 : Nat := 118140960795 + 471994 * 2 ^ 59
def prefixEnd_471994 : Nat := 4983230072969 + 3 ^ 40 * 471994 * 2
def baseEnd_471994 : Nat := 107715461350369580001931

theorem tailTrace_471994 : CollatzResearch.WordTrace tailWord_471994 prefixEnd_471994 107715461350369580001931 := by
  unfold tailWord_471994
  simp only [CollatzResearch.WordTrace]
  refine ⟨4303758863013455750651759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11476690301369215335071357 4303758863013455750651759)
  ·
    refine ⟨6455638294520183625977639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4303758863013455750651759 6455638294520183625977639)
    ·
      refine ⟨9683457441780275438966459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6455638294520183625977639 9683457441780275438966459)
      ·
        refine ⟨14525186162670413158449689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9683457441780275438966459 14525186162670413158449689)
        ·
          refine ⟨10893889622002809868837267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14525186162670413158449689 10893889622002809868837267)
          ·
            refine ⟨16340834433004214803255901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10893889622002809868837267 16340834433004214803255901)
            ·
              refine ⟨6127812912376580551220963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16340834433004214803255901 6127812912376580551220963)
              ·
                refine ⟨9191719368564870826831445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6127812912376580551220963 9191719368564870826831445)
                ·
                  refine ⟨107715461350369580001931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9191719368564870826831445 107715461350369580001931)
                  ·
                    rfl

theorem cell21_471994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_471994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_471994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_471994 prefixEnd_471994 := by exact prefixLift 471994
  have htrace : WordTrace (prefixWord ++ tailWord_471994) baseStart_471994 baseEnd_471994 := by
    simpa [prefixWord, tailWord_471994, baseEnd_471994] using wordTrace_append hprefix tailTrace_471994
  have hstable : (prefixWord ++ tailWord_471994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471994).length < 2 ^ (prefixWord ++ tailWord_471994).sum := by decide
  have hdescent : baseEnd_471994 < baseStart_471994 := by decide
  rcases family_descends (prefixWord ++ tailWord_471994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472006 : List Nat := [6, 1, 3, 1, 2, 1, 1, 1, 5]
def baseStart_472006 : Nat := 118140960795 + 472006 * 2 ^ 59
def prefixEnd_472006 : Nat := 4983230072969 + 3 ^ 40 * 472006 * 2
def baseEnd_472006 : Nat := 107718199913860225801907

theorem tailTrace_472006 : CollatzResearch.WordTrace tailWord_472006 prefixEnd_472006 107718199913860225801907 := by
  unfold tailWord_472006
  simp only [CollatzResearch.WordTrace]
  refine ⟨537983535250323407876371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11476982085340232701362581 537983535250323407876371)
  ·
    refine ⟨806975302875485111814557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 537983535250323407876371 806975302875485111814557)
    ·
      refine ⟨302615738578306916930459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 806975302875485111814557 302615738578306916930459)
      ·
        refine ⟨453923607867460375395689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302615738578306916930459 453923607867460375395689)
        ·
          refine ⟨340442705900595281546767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453923607867460375395689 340442705900595281546767)
          ·
            refine ⟨510664058850892922320151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340442705900595281546767 510664058850892922320151)
            ·
              refine ⟨765996088276339383480227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510664058850892922320151 765996088276339383480227)
              ·
                refine ⟨1148994132414509075220341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 765996088276339383480227 1148994132414509075220341)
                ·
                  refine ⟨107718199913860225801907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1148994132414509075220341 107718199913860225801907)
                  ·
                    rfl

theorem cell21_472006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_472006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_472006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_472006 prefixEnd_472006 := by exact prefixLift 472006
  have htrace : WordTrace (prefixWord ++ tailWord_472006) baseStart_472006 baseEnd_472006 := by
    simpa [prefixWord, tailWord_472006, baseEnd_472006] using wordTrace_append hprefix tailTrace_472006
  have hstable : (prefixWord ++ tailWord_472006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472006).length < 2 ^ (prefixWord ++ tailWord_472006).sum := by decide
  have hdescent : baseEnd_472006 < baseStart_472006 := by decide
  rcases family_descends (prefixWord ++ tailWord_472006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472025 : List Nat := [1, 2, 1, 2, 5, 1, 1, 8]
def baseStart_472025 : Nat := 118140960795 + 472025 * 2 ^ 59
def prefixEnd_472025 : Nat := 4983230072969 + 3 ^ 40 * 472025 * 2
def baseEnd_472025 : Nat := 35907511990906804995067

theorem tailTrace_472025 : CollatzResearch.WordTrace tailWord_472025 prefixEnd_472025 35907511990906804995067 := by
  unfold tailWord_472025
  simp only [CollatzResearch.WordTrace]
  refine ⟨17216166114941515296985529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11477444076627676864657019 17216166114941515296985529)
  ·
    refine ⟨12912124586206136472739147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17216166114941515296985529 12912124586206136472739147)
    ·
      refine ⟨19368186879309204709108721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12912124586206136472739147 19368186879309204709108721)
      ·
        refine ⟨14526140159481903531831541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19368186879309204709108721 14526140159481903531831541)
        ·
          refine ⟨1361825639951428456109207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14526140159481903531831541 1361825639951428456109207)
          ·
            refine ⟨2042738459927142684163811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1361825639951428456109207 2042738459927142684163811)
            ·
              refine ⟨3064107689890714026245717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2042738459927142684163811 3064107689890714026245717)
              ·
                refine ⟨35907511990906804995067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3064107689890714026245717 35907511990906804995067)
                ·
                  rfl

theorem cell21_472025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 8].length) (baseStart_472025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_472025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_472025 prefixEnd_472025 := by exact prefixLift 472025
  have htrace : WordTrace (prefixWord ++ tailWord_472025) baseStart_472025 baseEnd_472025 := by
    simpa [prefixWord, tailWord_472025, baseEnd_472025] using wordTrace_append hprefix tailTrace_472025
  have hstable : (prefixWord ++ tailWord_472025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472025).length < 2 ^ (prefixWord ++ tailWord_472025).sum := by decide
  have hdescent : baseEnd_472025 < baseStart_472025 := by decide
  rcases family_descends (prefixWord ++ tailWord_472025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472115 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 9]
def baseStart_472115 : Nat := 118140960795 + 472115 * 2 ^ 59
def prefixEnd_472115 : Nat := 4983230072969 + 3 ^ 40 * 472115 * 2
def baseEnd_472115 : Nat := 107743075198900258485017

theorem tailTrace_472115 : CollatzResearch.WordTrace tailWord_472115 prefixEnd_472115 107743075198900258485017 := by
  unfold tailWord_472115
  simp only [CollatzResearch.WordTrace]
  refine ⟨17219448684615460667761799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11479632456410307111841199 17219448684615460667761799)
  ·
    refine ⟨25829173026923191001642699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17219448684615460667761799 25829173026923191001642699)
    ·
      refine ⟨38743759540384786502464049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25829173026923191001642699 38743759540384786502464049)
      ·
        refine ⟨29057819655288589876848037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38743759540384786502464049 29057819655288589876848037)
        ·
          refine ⟨5448341185366610601909007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29057819655288589876848037 5448341185366610601909007)
          ·
            refine ⟨8172511778049915902863511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5448341185366610601909007 8172511778049915902863511)
            ·
              refine ⟨12258767667074873854295267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8172511778049915902863511 12258767667074873854295267)
              ·
                refine ⟨18388151500612310781442901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12258767667074873854295267 18388151500612310781442901)
                ·
                  refine ⟨107743075198900258485017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18388151500612310781442901 107743075198900258485017)
                  ·
                    rfl

theorem cell21_472115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 9].length) (baseStart_472115 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_472115 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_472115 prefixEnd_472115 := by exact prefixLift 472115
  have htrace : WordTrace (prefixWord ++ tailWord_472115) baseStart_472115 baseEnd_472115 := by
    simpa [prefixWord, tailWord_472115, baseEnd_472115] using wordTrace_append hprefix tailTrace_472115
  have hstable : (prefixWord ++ tailWord_472115).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472115).length < 2 ^ (prefixWord ++ tailWord_472115).sum := by decide
  have hdescent : baseEnd_472115 < baseStart_472115 := by decide
  rcases family_descends (prefixWord ++ tailWord_472115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472118 : List Nat := [5, 1, 2, 1, 1, 3, 8]
def baseStart_472118 : Nat := 118140960795 + 472118 * 2 ^ 59
def prefixEnd_472118 : Nat := 4983230072969 + 3 ^ 40 * 472118 * 2
def baseEnd_472118 : Nat := 11971528871085879992779

theorem tailTrace_472118 : CollatzResearch.WordTrace tailWord_472118 prefixEnd_472118 11971528871085879992779 := by
  unfold tailWord_472118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1076222381475287011257563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11479705402403061453414005 1076222381475287011257563)
  ·
    refine ⟨1614333572212930516886345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1076222381475287011257563 1614333572212930516886345)
    ·
      refine ⟨1210750179159697887664759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1614333572212930516886345 1210750179159697887664759)
      ·
        refine ⟨1816125268739546831497139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1210750179159697887664759 1816125268739546831497139)
        ·
          refine ⟨2724187903109320247245709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1816125268739546831497139 2724187903109320247245709)
          ·
            refine ⟨1021570463665995092717141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2724187903109320247245709 1021570463665995092717141)
            ·
              refine ⟨11971528871085879992779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1021570463665995092717141 11971528871085879992779)
              ·
                rfl

theorem cell21_472118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 8].length) (baseStart_472118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_472118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_472118 prefixEnd_472118 := by exact prefixLift 472118
  have htrace : WordTrace (prefixWord ++ tailWord_472118) baseStart_472118 baseEnd_472118 := by
    simpa [prefixWord, tailWord_472118, baseEnd_472118] using wordTrace_append hprefix tailTrace_472118
  have hstable : (prefixWord ++ tailWord_472118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472118).length < 2 ^ (prefixWord ++ tailWord_472118).sum := by decide
  have hdescent : baseEnd_472118 < baseStart_472118 := by decide
  rcases family_descends (prefixWord ++ tailWord_472118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472197 : List Nat := [1, 3, 1, 1, 6, 2, 2, 1, 4]
def baseStart_472197 : Nat := 118140960795 + 472197 * 2 ^ 59
def prefixEnd_472197 : Nat := 4983230072969 + 3 ^ 40 * 472197 * 2
def baseEnd_472197 : Nat := 107761788716086338118183

theorem tailTrace_472197 : CollatzResearch.WordTrace tailWord_472197 prefixEnd_472197 107761788716086338118183 := by
  unfold tailWord_472197
  simp only [CollatzResearch.WordTrace]
  refine ⟨17222439470318388672246845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11481626313545592448164563 17222439470318388672246845)
  ·
    refine ⟨6458414801369395752092567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17222439470318388672246845 6458414801369395752092567)
    ·
      refine ⟨9687622202054093628138851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6458414801369395752092567 9687622202054093628138851)
      ·
        refine ⟨14531433303081140442208277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9687622202054093628138851 14531433303081140442208277)
        ·
          refine ⟨681160936081928458228513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14531433303081140442208277 681160936081928458228513)
          ·
            refine ⟨510870702061446343671385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 681160936081928458228513 510870702061446343671385)
            ·
              refine ⟨383153026546084757753539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 510870702061446343671385 383153026546084757753539)
              ·
                refine ⟨574729539819127136630309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383153026546084757753539 574729539819127136630309)
                ·
                  refine ⟨107761788716086338118183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 574729539819127136630309 107761788716086338118183)
                  ·
                    rfl

theorem cell21_472197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_472197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_472197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_472197 prefixEnd_472197 := by exact prefixLift 472197
  have htrace : WordTrace (prefixWord ++ tailWord_472197) baseStart_472197 baseEnd_472197 := by
    simpa [prefixWord, tailWord_472197, baseEnd_472197] using wordTrace_append hprefix tailTrace_472197
  have hstable : (prefixWord ++ tailWord_472197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472197).length < 2 ^ (prefixWord ++ tailWord_472197).sum := by decide
  have hdescent : baseEnd_472197 < baseStart_472197 := by decide
  rcases family_descends (prefixWord ++ tailWord_472197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472225 : List Nat := [1, 2, 3, 3, 1, 1, 2, 5, 3]
def baseStart_472225 : Nat := 118140960795 + 472225 * 2 ^ 59
def prefixEnd_472225 : Nat := 4983230072969 + 3 ^ 40 * 472225 * 2
def baseEnd_472225 : Nat := 107768178697564511651459

theorem tailTrace_472225 : CollatzResearch.WordTrace tailWord_472225 prefixEnd_472225 107768178697564511651459 := by
  unfold tailWord_472225
  simp only [CollatzResearch.WordTrace]
  refine ⟨17223460714216949454266129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11482307142811299636177419 17223460714216949454266129)
  ·
    refine ⟨12917595535662712090699597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17223460714216949454266129 12917595535662712090699597)
    ·
      refine ⟨4844098325873517034012349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12917595535662712090699597 4844098325873517034012349)
      ·
        refine ⟨1816536872202568887754631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4844098325873517034012349 1816536872202568887754631)
        ·
          refine ⟨2724805308303853331631947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1816536872202568887754631 2724805308303853331631947)
          ·
            refine ⟨4087207962455779997447921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2724805308303853331631947 4087207962455779997447921)
            ·
              refine ⟨3065405971841834998085941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4087207962455779997447921 3065405971841834998085941)
              ·
                refine ⟨287381809860172031070557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3065405971841834998085941 287381809860172031070557)
                ·
                  refine ⟨107768178697564511651459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 287381809860172031070557 107768178697564511651459)
                  ·
                    rfl

theorem cell21_472225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 5, 3].length) (baseStart_472225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_472225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_472225 prefixEnd_472225 := by exact prefixLift 472225
  have htrace : WordTrace (prefixWord ++ tailWord_472225) baseStart_472225 baseEnd_472225 := by
    simpa [prefixWord, tailWord_472225, baseEnd_472225] using wordTrace_append hprefix tailTrace_472225
  have hstable : (prefixWord ++ tailWord_472225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472225).length < 2 ^ (prefixWord ++ tailWord_472225).sum := by decide
  have hdescent : baseEnd_472225 < baseStart_472225 := by decide
  rcases family_descends (prefixWord ++ tailWord_472225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472242 : List Nat := [3, 2, 1, 1, 1, 4, 4, 2, 3]
def baseStart_472242 : Nat := 118140960795 + 472242 * 2 ^ 59
def prefixEnd_472242 : Nat := 4983230072969 + 3 ^ 40 * 472242 * 2
def baseEnd_472242 : Nat := 107772058329176259868091

theorem tailTrace_472242 : CollatzResearch.WordTrace tailWord_472242 prefixEnd_472242 107772058329176259868091 := by
  unfold tailWord_472242
  simp only [CollatzResearch.WordTrace]
  refine ⟨4306020188788840339408745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11482720503436907571756653 4306020188788840339408745)
  ·
    refine ⟨3229515141591630254556559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4306020188788840339408745 3229515141591630254556559)
    ·
      refine ⟨4844272712387445381834839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3229515141591630254556559 4844272712387445381834839)
      ·
        refine ⟨7266409068581168072752259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4844272712387445381834839 7266409068581168072752259)
        ·
          refine ⟨10899613602871752109128389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7266409068581168072752259 10899613602871752109128389)
          ·
            refine ⟨2043677550538453520461573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10899613602871752109128389 2043677550538453520461573)
            ·
              refine ⟨383189540725960035086545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2043677550538453520461573 383189540725960035086545)
              ·
                refine ⟨287392155544470026314909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 383189540725960035086545 287392155544470026314909)
                ·
                  refine ⟨107772058329176259868091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 287392155544470026314909 107772058329176259868091)
                  ·
                    rfl

theorem cell21_472242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_472242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_472242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_472242 prefixEnd_472242 := by exact prefixLift 472242
  have htrace : WordTrace (prefixWord ++ tailWord_472242) baseStart_472242 baseEnd_472242 := by
    simpa [prefixWord, tailWord_472242, baseEnd_472242] using wordTrace_append hprefix tailTrace_472242
  have hstable : (prefixWord ++ tailWord_472242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472242).length < 2 ^ (prefixWord ++ tailWord_472242).sum := by decide
  have hdescent : baseEnd_472242 < baseStart_472242 := by decide
  rcases family_descends (prefixWord ++ tailWord_472242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472253 : List Nat := [1, 4, 1, 2, 1, 1, 5, 6]
def baseStart_472253 : Nat := 118140960795 + 472253 * 2 ^ 59
def prefixEnd_472253 : Nat := 4983230072969 + 3 ^ 40 * 472253 * 2
def baseEnd_472253 : Nat := 35924856226347561728245

theorem tailTrace_472253 : CollatzResearch.WordTrace tailWord_472253 prefixEnd_472253 35924856226347561728245 := by
  unfold tailWord_472253
  simp only [CollatzResearch.WordTrace]
  refine ⟨17224481958115510236285413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11482987972077006824190275 17224481958115510236285413)
  ·
    refine ⟨3229590367146658169303515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17224481958115510236285413 3229590367146658169303515)
    ·
      refine ⟨4844385550719987253955273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3229590367146658169303515 4844385550719987253955273)
      ·
        refine ⟨3633289163039990440466455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4844385550719987253955273 3633289163039990440466455)
        ·
          refine ⟨5449933744559985660699683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3633289163039990440466455 5449933744559985660699683)
          ·
            refine ⟨8174900616839978491049525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5449933744559985660699683 8174900616839978491049525)
            ·
              refine ⟨766396932828747983535893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8174900616839978491049525 766396932828747983535893)
              ·
                refine ⟨35924856226347561728245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 766396932828747983535893 35924856226347561728245)
                ·
                  rfl

theorem cell21_472253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 6].length) (baseStart_472253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_472253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_472253 prefixEnd_472253 := by exact prefixLift 472253
  have htrace : WordTrace (prefixWord ++ tailWord_472253) baseStart_472253 baseEnd_472253 := by
    simpa [prefixWord, tailWord_472253, baseEnd_472253] using wordTrace_append hprefix tailTrace_472253
  have hstable : (prefixWord ++ tailWord_472253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472253).length < 2 ^ (prefixWord ++ tailWord_472253).sum := by decide
  have hdescent : baseEnd_472253 < baseStart_472253 := by decide
  rcases family_descends (prefixWord ++ tailWord_472253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472301 : List Nat := [1, 5, 1, 2, 2, 2, 2, 1, 5]
def baseStart_472301 : Nat := 118140960795 + 472301 * 2 ^ 59
def prefixEnd_472301 : Nat := 4983230072969 + 3 ^ 40 * 472301 * 2
def baseEnd_472301 : Nat := 107785522933005268384637

theorem tailTrace_472301 : CollatzResearch.WordTrace tailWord_472301 prefixEnd_472301 107785522933005268384637 := by
  unfold tailWord_472301
  simp only [CollatzResearch.WordTrace]
  refine ⟨17226232661941614434032757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11484155107961076289355171 17226232661941614434032757)
  ·
    refine ⟨1614959312057026353190571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17226232661941614434032757 1614959312057026353190571)
    ·
      refine ⟨2422438968085539529785857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1614959312057026353190571 2422438968085539529785857)
      ·
        refine ⟨1816829226064154647339393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2422438968085539529785857 1816829226064154647339393)
        ·
          refine ⟨1362621919548115985504545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1816829226064154647339393 1362621919548115985504545)
          ·
            refine ⟨1021966439661086989128409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1362621919548115985504545 1021966439661086989128409)
            ·
              refine ⟨766474829745815241846307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1021966439661086989128409 766474829745815241846307)
              ·
                refine ⟨1149712244618722862769461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 766474829745815241846307 1149712244618722862769461)
                ·
                  refine ⟨107785522933005268384637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1149712244618722862769461 107785522933005268384637)
                  ·
                    rfl

theorem cell21_472301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_472301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_472301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_472301 prefixEnd_472301 := by exact prefixLift 472301
  have htrace : WordTrace (prefixWord ++ tailWord_472301) baseStart_472301 baseEnd_472301 := by
    simpa [prefixWord, tailWord_472301, baseEnd_472301] using wordTrace_append hprefix tailTrace_472301
  have hstable : (prefixWord ++ tailWord_472301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472301).length < 2 ^ (prefixWord ++ tailWord_472301).sum := by decide
  have hdescent : baseEnd_472301 < baseStart_472301 := by decide
  rcases family_descends (prefixWord ++ tailWord_472301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472526 : List Nat := [4, 1, 1, 1, 2, 1, 4, 1, 6]
def baseStart_472526 : Nat := 118140960795 + 472526 * 2 ^ 59
def prefixEnd_472526 : Nat := 4983230072969 + 3 ^ 40 * 472526 * 2
def baseEnd_472526 : Nat := 107836870998454877134177

theorem tailTrace_472526 : CollatzResearch.WordTrace tailWord_472526 prefixEnd_472526 107836870998454877134177 := by
  unfold tailWord_472526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2154304885765809732621679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11489626057417651907315621 2154304885765809732621679)
  ·
    refine ⟨3231457328648714598932519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2154304885765809732621679 3231457328648714598932519)
    ·
      refine ⟨4847185992973071898398779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3231457328648714598932519 4847185992973071898398779)
      ·
        refine ⟨7270778989459607847598169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4847185992973071898398779 7270778989459607847598169)
        ·
          refine ⟨5453084242094705885698627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7270778989459607847598169 5453084242094705885698627)
          ·
            refine ⟨8179626363142058828547941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5453084242094705885698627 8179626363142058828547941)
            ·
              refine ⟨1533679943089136030352739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8179626363142058828547941 1533679943089136030352739)
              ·
                refine ⟨2300519914633704045529109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1533679943089136030352739 2300519914633704045529109)
                ·
                  refine ⟨107836870998454877134177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2300519914633704045529109 107836870998454877134177)
                  ·
                    rfl

theorem cell21_472526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_472526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_472526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_472526 prefixEnd_472526 := by exact prefixLift 472526
  have htrace : WordTrace (prefixWord ++ tailWord_472526) baseStart_472526 baseEnd_472526 := by
    simpa [prefixWord, tailWord_472526, baseEnd_472526] using wordTrace_append hprefix tailTrace_472526
  have hstable : (prefixWord ++ tailWord_472526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472526).length < 2 ^ (prefixWord ++ tailWord_472526).sum := by decide
  have hdescent : baseEnd_472526 < baseStart_472526 := by decide
  rcases family_descends (prefixWord ++ tailWord_472526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472574 : List Nat := [4, 2, 2, 3, 1, 9]
def baseStart_472574 : Nat := 118140960795 + 472574 * 2 ^ 59
def prefixEnd_472574 : Nat := 4983230072969 + 3 ^ 40 * 472574 * 2
def baseEnd_472574 : Nat := 3994363898237683716077

theorem tailTrace_472574 : CollatzResearch.WordTrace tailWord_472574 prefixEnd_472574 3994363898237683716077 := by
  unfold tailWord_472574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2154523723744072757340097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11490793193301721372480517 2154523723744072757340097)
  ·
    refine ⟨1615892792808054568005073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2154523723744072757340097 1615892792808054568005073)
    ·
      refine ⟨1211919594606040926003805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1615892792808054568005073 1211919594606040926003805)
      ·
        refine ⟨454469847977265347251427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1211919594606040926003805 454469847977265347251427)
        ·
          refine ⟨681704771965898020877141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454469847977265347251427 681704771965898020877141)
          ·
            refine ⟨3994363898237683716077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 681704771965898020877141 3994363898237683716077)
            ·
              rfl

theorem cell21_472574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 9].length) (baseStart_472574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_472574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_472574 prefixEnd_472574 := by exact prefixLift 472574
  have htrace : WordTrace (prefixWord ++ tailWord_472574) baseStart_472574 baseEnd_472574 := by
    simpa [prefixWord, tailWord_472574, baseEnd_472574] using wordTrace_append hprefix tailTrace_472574
  have hstable : (prefixWord ++ tailWord_472574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472574).length < 2 ^ (prefixWord ++ tailWord_472574).sum := by decide
  have hdescent : baseEnd_472574 < baseStart_472574 := by decide
  rcases family_descends (prefixWord ++ tailWord_472574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472580 : List Nat := [2, 3, 2, 3, 3, 1, 2, 2, 3]
def baseStart_472580 : Nat := 118140960795 + 472580 * 2 ^ 59
def prefixEnd_472580 : Nat := 4983230072969 + 3 ^ 40 * 472580 * 2
def baseEnd_472580 : Nat := 107849194534162783234067

theorem tailTrace_472580 : CollatzResearch.WordTrace tailWord_472580 prefixEnd_472580 107849194534162783234067 := by
  unfold tailWord_472580
  simp only [CollatzResearch.WordTrace]
  refine ⟨8618204313965422541719597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11490939085287230055626129 8618204313965422541719597)
  ·
    refine ⟨3231826617737033453144849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8618204313965422541719597 3231826617737033453144849)
    ·
      refine ⟨2423869963302775089858637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3231826617737033453144849 2423869963302775089858637)
      ·
        refine ⟨908951236238540658696989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2423869963302775089858637 908951236238540658696989)
        ·
          refine ⟨340856713589452747011371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 908951236238540658696989 340856713589452747011371)
          ·
            refine ⟨511285070384179120517057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340856713589452747011371 511285070384179120517057)
            ·
              refine ⟨383463802788134340387793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 511285070384179120517057 383463802788134340387793)
              ·
                refine ⟨287597852091100755290845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 383463802788134340387793 287597852091100755290845)
                ·
                  refine ⟨107849194534162783234067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 287597852091100755290845 107849194534162783234067)
                  ·
                    rfl

theorem cell21_472580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_472580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_472580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_472580 prefixEnd_472580 := by exact prefixLift 472580
  have htrace : WordTrace (prefixWord ++ tailWord_472580) baseStart_472580 baseEnd_472580 := by
    simpa [prefixWord, tailWord_472580, baseEnd_472580] using wordTrace_append hprefix tailTrace_472580
  have hstable : (prefixWord ++ tailWord_472580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472580).length < 2 ^ (prefixWord ++ tailWord_472580).sum := by decide
  have hdescent : baseEnd_472580 < baseStart_472580 := by decide
  rcases family_descends (prefixWord ++ tailWord_472580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472622 : List Nat := [4, 1, 3, 1, 2, 2, 2, 3, 3]
def baseStart_472622 : Nat := 118140960795 + 472622 * 2 ^ 59
def prefixEnd_472622 : Nat := 4983230072969 + 3 ^ 40 * 472622 * 2
def baseEnd_472622 : Nat := 107858779506380043533981

theorem tailTrace_472622 : CollatzResearch.WordTrace tailWord_472622 prefixEnd_472622 107858779506380043533981 := by
  unfold tailWord_472622
  simp only [CollatzResearch.WordTrace]
  refine ⟨2154742561722335782058515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11491960329185790837645413 2154742561722335782058515)
  ·
    refine ⟨3232113842583503673087773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2154742561722335782058515 3232113842583503673087773)
    ·
      refine ⟨1212042690968813877407915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3232113842583503673087773 1212042690968813877407915)
      ·
        refine ⟨1818064036453220816111873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1212042690968813877407915 1818064036453220816111873)
        ·
          refine ⟨1363548027339915612083905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1818064036453220816111873 1363548027339915612083905)
          ·
            refine ⟨1022661020504936709062929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1363548027339915612083905 1022661020504936709062929)
            ·
              refine ⟨766995765378702531797197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1022661020504936709062929 766995765378702531797197)
              ·
                refine ⟨287623412017013449423949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 766995765378702531797197 287623412017013449423949)
                ·
                  refine ⟨107858779506380043533981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 287623412017013449423949 107858779506380043533981)
                  ·
                    rfl

theorem cell21_472622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_472622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_472622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_472622 prefixEnd_472622 := by exact prefixLift 472622
  have htrace : WordTrace (prefixWord ++ tailWord_472622) baseStart_472622 baseEnd_472622 := by
    simpa [prefixWord, tailWord_472622, baseEnd_472622] using wordTrace_append hprefix tailTrace_472622
  have hstable : (prefixWord ++ tailWord_472622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472622).length < 2 ^ (prefixWord ++ tailWord_472622).sum := by decide
  have hdescent : baseEnd_472622 < baseStart_472622 := by decide
  rcases family_descends (prefixWord ++ tailWord_472622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472636 : List Nat := [2, 2, 2, 2, 4, 2, 1, 2, 4]
def baseStart_472636 : Nat := 118140960795 + 472636 * 2 ^ 59
def prefixEnd_472636 : Nat := 4983230072969 + 3 ^ 40 * 472636 * 2
def baseEnd_472636 : Nat := 107861974497119130300619

theorem tailTrace_472636 : CollatzResearch.WordTrace tailWord_472636 prefixEnd_472636 107861974497119130300619 := by
  unfold tailWord_472636
  simp only [CollatzResearch.WordTrace]
  refine ⟨8619225557863983323738881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11492300743818644431651841 8619225557863983323738881)
  ·
    refine ⟨6464419168397987492804161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8619225557863983323738881 6464419168397987492804161)
    ·
      refine ⟨4848314376298490619603121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6464419168397987492804161 4848314376298490619603121)
      ·
        refine ⟨3636235782223867964702341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4848314376298490619603121 3636235782223867964702341)
        ·
          refine ⟨681794209166975243381689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3636235782223867964702341 681794209166975243381689)
          ·
            refine ⟨511345656875231432536267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 681794209166975243381689 511345656875231432536267)
            ·
              refine ⟨767018485312847148804401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511345656875231432536267 767018485312847148804401)
              ·
                refine ⟨575263863984635361603301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 767018485312847148804401 575263863984635361603301)
                ·
                  refine ⟨107861974497119130300619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 575263863984635361603301 107861974497119130300619)
                  ·
                    rfl

theorem cell21_472636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_472636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_472636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_472636 prefixEnd_472636 := by exact prefixLift 472636
  have htrace : WordTrace (prefixWord ++ tailWord_472636) baseStart_472636 baseEnd_472636 := by
    simpa [prefixWord, tailWord_472636, baseEnd_472636] using wordTrace_append hprefix tailTrace_472636
  have hstable : (prefixWord ++ tailWord_472636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472636).length < 2 ^ (prefixWord ++ tailWord_472636).sum := by decide
  have hdescent : baseEnd_472636 < baseStart_472636 := by decide
  rcases family_descends (prefixWord ++ tailWord_472636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472653 : List Nat := [1, 6, 1, 1, 3, 1, 3, 1, 4]
def baseStart_472653 : Nat := 118140960795 + 472653 * 2 ^ 59
def prefixEnd_472653 : Nat := 4983230072969 + 3 ^ 40 * 472653 * 2
def baseEnd_472653 : Nat := 107865854128730878517251

theorem tailTrace_472653 : CollatzResearch.WordTrace tailWord_472653 prefixEnd_472653 107865854128730878517251 := by
  unfold tailWord_472653
  simp only [CollatzResearch.WordTrace]
  refine ⟨17239071156666378550846613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11492714104444252367231075 17239071156666378550846613)
  ·
    refine ⟨808081460468736494570935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17239071156666378550846613 808081460468736494570935)
    ·
      refine ⟨1212122190703104741856403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 808081460468736494570935 1212122190703104741856403)
      ·
        refine ⟨1818183286054657112784605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1212122190703104741856403 1818183286054657112784605)
        ·
          refine ⟨681818732270496417294227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1818183286054657112784605 681818732270496417294227)
          ·
            refine ⟨1022728098405744625941341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681818732270496417294227 1022728098405744625941341)
            ·
              refine ⟨383523036902154234728003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1022728098405744625941341 383523036902154234728003)
              ·
                refine ⟨575284555353231352092005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383523036902154234728003 575284555353231352092005)
                ·
                  refine ⟨107865854128730878517251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 575284555353231352092005 107865854128730878517251)
                  ·
                    rfl

theorem cell21_472653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_472653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_472653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_472653 prefixEnd_472653 := by exact prefixLift 472653
  have htrace : WordTrace (prefixWord ++ tailWord_472653) baseStart_472653 baseEnd_472653 := by
    simpa [prefixWord, tailWord_472653, baseEnd_472653] using wordTrace_append hprefix tailTrace_472653
  have hstable : (prefixWord ++ tailWord_472653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472653).length < 2 ^ (prefixWord ++ tailWord_472653).sum := by decide
  have hdescent : baseEnd_472653 < baseStart_472653 := by decide
  rcases family_descends (prefixWord ++ tailWord_472653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472712 : List Nat := [2, 1, 3, 5, 1, 1, 1, 3, 4]
def baseStart_472712 : Nat := 118140960795 + 472712 * 2 ^ 59
def prefixEnd_472712 : Nat := 4983230072969 + 3 ^ 40 * 472712 * 2
def baseEnd_472712 : Nat := 107879318732559887033797

theorem tailTrace_472712 : CollatzResearch.WordTrace tailWord_472712 prefixEnd_472712 107879318732559887033797 := by
  unfold tailWord_472712
  simp only [CollatzResearch.WordTrace]
  refine ⟨8620611531726315813622195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11494148708968421084829593 8620611531726315813622195)
  ·
    refine ⟨12930917297589473720433293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8620611531726315813622195 12930917297589473720433293)
    ·
      refine ⟨4849093986596052645162485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12930917297589473720433293 4849093986596052645162485)
      ·
        refine ⟨454602561243379935483983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4849093986596052645162485 454602561243379935483983)
        ·
          refine ⟨681903841865069903225975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454602561243379935483983 681903841865069903225975)
          ·
            refine ⟨1022855762797604854838963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681903841865069903225975 1022855762797604854838963)
            ·
              refine ⟨1534283644196407282258445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1022855762797604854838963 1534283644196407282258445)
              ·
                refine ⟨575356366573652730846917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1534283644196407282258445 575356366573652730846917)
                ·
                  refine ⟨107879318732559887033797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 575356366573652730846917 107879318732559887033797)
                  ·
                    rfl

theorem cell21_472712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 4].length) (baseStart_472712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_472712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_472712 prefixEnd_472712 := by exact prefixLift 472712
  have htrace : WordTrace (prefixWord ++ tailWord_472712) baseStart_472712 baseEnd_472712 := by
    simpa [prefixWord, tailWord_472712, baseEnd_472712] using wordTrace_append hprefix tailTrace_472712
  have hstable : (prefixWord ++ tailWord_472712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472712).length < 2 ^ (prefixWord ++ tailWord_472712).sum := by decide
  have hdescent : baseEnd_472712 < baseStart_472712 := by decide
  rcases family_descends (prefixWord ++ tailWord_472712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472754 : List Nat := [3, 2, 1, 1, 1, 2, 3, 4, 4]
def baseStart_472754 : Nat := 118140960795 + 472754 * 2 ^ 59
def prefixEnd_472754 : Nat := 4983230072969 + 3 ^ 40 * 472754 * 2
def baseEnd_472754 : Nat := 107888903704777147333711

theorem tailTrace_472754 : CollatzResearch.WordTrace tailWord_472754 prefixEnd_472754 107888903704777147333711 := by
  unfold tailWord_472754
  simp only [CollatzResearch.WordTrace]
  refine ⟨4310688732325118200068329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11495169952866981866848877 4310688732325118200068329)
  ·
    refine ⟨3233016549243838650051247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4310688732325118200068329 3233016549243838650051247)
    ·
      refine ⟨4849524823865757975076871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3233016549243838650051247 4849524823865757975076871)
      ·
        refine ⟨7274287235798636962615307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4849524823865757975076871 7274287235798636962615307)
        ·
          refine ⟨10911430853697955443922961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7274287235798636962615307 10911430853697955443922961)
          ·
            refine ⟨8183573140273466582942221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10911430853697955443922961 8183573140273466582942221)
            ·
              refine ⟨3068839927602549968603333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8183573140273466582942221 3068839927602549968603333)
              ·
                refine ⟨575407486425478119113125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3068839927602549968603333 575407486425478119113125)
                ·
                  refine ⟨107888903704777147333711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 575407486425478119113125 107888903704777147333711)
                  ·
                    rfl

theorem cell21_472754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_472754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_472754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_472754 prefixEnd_472754 := by exact prefixLift 472754
  have htrace : WordTrace (prefixWord ++ tailWord_472754) baseStart_472754 baseEnd_472754 := by
    simpa [prefixWord, tailWord_472754, baseEnd_472754] using wordTrace_append hprefix tailTrace_472754
  have hstable : (prefixWord ++ tailWord_472754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472754).length < 2 ^ (prefixWord ++ tailWord_472754).sum := by decide
  have hdescent : baseEnd_472754 < baseStart_472754 := by decide
  rcases family_descends (prefixWord ++ tailWord_472754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472774 : List Nat := [6, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_472774 : Nat := 118140960795 + 472774 * 2 ^ 59
def prefixEnd_472774 : Nat := 4983230072969 + 3 ^ 40 * 472774 * 2
def baseEnd_472774 : Nat := 107893467977261557000337

theorem tailTrace_472774 : CollatzResearch.WordTrace tailWord_472774 prefixEnd_472774 107893467977261557000337 := by
  unfold tailWord_472774
  simp only [CollatzResearch.WordTrace]
  refine ⟨538858887163375506750043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11495656259485344144000917 538858887163375506750043)
  ·
    refine ⟨808288330745063260125065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 538858887163375506750043 808288330745063260125065)
    ·
      refine ⟨606216248058797445093799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 808288330745063260125065 606216248058797445093799)
      ·
        refine ⟨909324372088196167640699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606216248058797445093799 909324372088196167640699)
        ·
          refine ⟨1363986558132294251461049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 909324372088196167640699 1363986558132294251461049)
          ·
            refine ⟨1022989918599220688595787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1363986558132294251461049 1022989918599220688595787)
            ·
              refine ⟨1534484877898831032893681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1022989918599220688595787 1534484877898831032893681)
              ·
                refine ⟨1150863658424123274670261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1534484877898831032893681 1150863658424123274670261)
                ·
                  refine ⟨107893467977261557000337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1150863658424123274670261 107893467977261557000337)
                  ·
                    rfl

theorem cell21_472774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_472774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_472774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_472774 prefixEnd_472774 := by exact prefixLift 472774
  have htrace : WordTrace (prefixWord ++ tailWord_472774) baseStart_472774 baseEnd_472774 := by
    simpa [prefixWord, tailWord_472774, baseEnd_472774] using wordTrace_append hprefix tailTrace_472774
  have hstable : (prefixWord ++ tailWord_472774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472774).length < 2 ^ (prefixWord ++ tailWord_472774).sum := by decide
  have hdescent : baseEnd_472774 < baseStart_472774 := by decide
  rcases family_descends (prefixWord ++ tailWord_472774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472785 : List Nat := [1, 2, 2, 1, 2, 5, 3, 5]
def baseStart_472785 : Nat := 118140960795 + 472785 * 2 ^ 59
def prefixEnd_472785 : Nat := 4983230072969 + 3 ^ 40 * 472785 * 2
def baseEnd_472785 : Nat := 35965326109042660772327

theorem tailTrace_472785 : CollatzResearch.WordTrace tailWord_472785 prefixEnd_472785 35965326109042660772327 := by
  unfold tailWord_472785
  simp only [CollatzResearch.WordTrace]
  refine ⟨17243885592188165094651809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11495923728125443396434539 17243885592188165094651809)
  ·
    refine ⟨12932914194141123820988857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17243885592188165094651809 12932914194141123820988857)
    ·
      refine ⟨9699685645605842865741643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12932914194141123820988857 9699685645605842865741643)
      ·
        refine ⟨14549528468408764298612465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9699685645605842865741643 14549528468408764298612465)
        ·
          refine ⟨10912146351306573223959349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14549528468408764298612465 10912146351306573223959349)
          ·
            refine ⟨1023013720434991239746189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10912146351306573223959349 1023013720434991239746189)
            ·
              refine ⟨383630145163121714904821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1023013720434991239746189 383630145163121714904821)
              ·
                refine ⟨35965326109042660772327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 383630145163121714904821 35965326109042660772327)
                ·
                  rfl

theorem cell21_472785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 5].length) (baseStart_472785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_472785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_472785 prefixEnd_472785 := by exact prefixLift 472785
  have htrace : WordTrace (prefixWord ++ tailWord_472785) baseStart_472785 baseEnd_472785 := by
    simpa [prefixWord, tailWord_472785, baseEnd_472785] using wordTrace_append hprefix tailTrace_472785
  have hstable : (prefixWord ++ tailWord_472785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472785).length < 2 ^ (prefixWord ++ tailWord_472785).sum := by decide
  have hdescent : baseEnd_472785 < baseStart_472785 := by decide
  rcases family_descends (prefixWord ++ tailWord_472785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472850 : List Nat := [3, 2, 4, 1, 1, 1, 3, 3, 3]
def baseStart_472850 : Nat := 118140960795 + 472850 * 2 ^ 59
def prefixEnd_472850 : Nat := 4983230072969 + 3 ^ 40 * 472850 * 2
def baseEnd_472850 : Nat := 107910812212702313733515

theorem tailTrace_472850 : CollatzResearch.WordTrace tailWord_472850 prefixEnd_472850 107910812212702313733515 := by
  unfold tailWord_472850
  simp only [CollatzResearch.WordTrace]
  refine ⟨4311564084238170298942001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11497504224635120797178669 4311564084238170298942001)
  ·
    refine ⟨3233673063178627724206501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4311564084238170298942001 3233673063178627724206501)
    ·
      refine ⟨606313699345992698288719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3233673063178627724206501 606313699345992698288719)
      ·
        refine ⟨909470549018989047433079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606313699345992698288719 909470549018989047433079)
        ·
          refine ⟨1364205823528483571149619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 909470549018989047433079 1364205823528483571149619)
          ·
            refine ⟨2046308735292725356724429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1364205823528483571149619 2046308735292725356724429)
            ·
              refine ⟨767365775734772008771661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2046308735292725356724429 767365775734772008771661)
              ·
                refine ⟨287762165900539503289373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 767365775734772008771661 287762165900539503289373)
                ·
                  refine ⟨107910812212702313733515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 287762165900539503289373 107910812212702313733515)
                  ·
                    rfl

theorem cell21_472850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_472850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_472850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_472850 prefixEnd_472850 := by exact prefixLift 472850
  have htrace : WordTrace (prefixWord ++ tailWord_472850) baseStart_472850 baseEnd_472850 := by
    simpa [prefixWord, tailWord_472850, baseEnd_472850] using wordTrace_append hprefix tailTrace_472850
  have hstable : (prefixWord ++ tailWord_472850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472850).length < 2 ^ (prefixWord ++ tailWord_472850).sum := by decide
  have hdescent : baseEnd_472850 < baseStart_472850 := by decide
  rcases family_descends (prefixWord ++ tailWord_472850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472878 : List Nat := [4, 1, 3, 2, 2, 1, 2, 6]
def baseStart_472878 : Nat := 118140960795 + 472878 * 2 ^ 59
def prefixEnd_472878 : Nat := 4983230072969 + 3 ^ 40 * 472878 * 2
def baseEnd_472878 : Nat := 35972400731393495755597

theorem tailTrace_472878 : CollatzResearch.WordTrace tailWord_472878 prefixEnd_472878 35972400731393495755597 := by
  unfold tailWord_472878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2155909697606405247223411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11498185053900827985191525 2155909697606405247223411)
  ·
    refine ⟨3233864546409607870835117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2155909697606405247223411 3233864546409607870835117)
    ·
      refine ⟨1212699204903602951563169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3233864546409607870835117 1212699204903602951563169)
      ·
        refine ⟨909524403677702213672377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1212699204903602951563169 909524403677702213672377)
        ·
          refine ⟨682143302758276660254283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 909524403677702213672377 682143302758276660254283)
          ·
            refine ⟨1023214954137414990381425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682143302758276660254283 1023214954137414990381425)
            ·
              refine ⟨767411215603061242786069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1023214954137414990381425 767411215603061242786069)
              ·
                refine ⟨35972400731393495755597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 767411215603061242786069 35972400731393495755597)
                ·
                  rfl

theorem cell21_472878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_472878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_472878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_472878 prefixEnd_472878 := by exact prefixLift 472878
  have htrace : WordTrace (prefixWord ++ tailWord_472878) baseStart_472878 baseEnd_472878 := by
    simpa [prefixWord, tailWord_472878, baseEnd_472878] using wordTrace_append hprefix tailTrace_472878
  have hstable : (prefixWord ++ tailWord_472878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472878).length < 2 ^ (prefixWord ++ tailWord_472878).sum := by decide
  have hdescent : baseEnd_472878 < baseStart_472878 := by decide
  rcases family_descends (prefixWord ++ tailWord_472878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472965 : List Nat := [1, 3, 1, 1, 3, 2, 2, 2, 6]
def baseStart_472965 : Nat := 118140960795 + 472965 * 2 ^ 59
def prefixEnd_472965 : Nat := 4983230072969 + 3 ^ 40 * 472965 * 2
def baseEnd_472965 : Nat := 107937056779487669316613

theorem tailTrace_472965 : CollatzResearch.WordTrace tailWord_472965 prefixEnd_472965 107937056779487669316613 := by
  unfold tailWord_472965
  simp only [CollatzResearch.WordTrace]
  refine ⟨17250450731536055836204349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11500300487690703890802899 17250450731536055836204349)
  ·
    refine ⟨6468919024326020938576631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17250450731536055836204349 6468919024326020938576631)
    ·
      refine ⟨9703378536489031407864947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6468919024326020938576631 9703378536489031407864947)
      ·
        refine ⟨14555067804733547111797421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9703378536489031407864947 14555067804733547111797421)
        ·
          refine ⟨5458150426775080166924033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14555067804733547111797421 5458150426775080166924033)
          ·
            refine ⟨4093612820081310125193025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5458150426775080166924033 4093612820081310125193025)
            ·
              refine ⟨3070209615060982593894769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4093612820081310125193025 3070209615060982593894769)
              ·
                refine ⟨2302657211295736945421077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3070209615060982593894769 2302657211295736945421077)
                ·
                  refine ⟨107937056779487669316613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2302657211295736945421077 107937056779487669316613)
                  ·
                    rfl

theorem cell21_472965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_472965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_472965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_472965 prefixEnd_472965 := by exact prefixLift 472965
  have htrace : WordTrace (prefixWord ++ tailWord_472965) baseStart_472965 baseEnd_472965 := by
    simpa [prefixWord, tailWord_472965, baseEnd_472965] using wordTrace_append hprefix tailTrace_472965
  have hstable : (prefixWord ++ tailWord_472965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472965).length < 2 ^ (prefixWord ++ tailWord_472965).sum := by decide
  have hdescent : baseEnd_472965 < baseStart_472965 := by decide
  rcases family_descends (prefixWord ++ tailWord_472965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473013 : List Nat := [1, 3, 3, 2, 1, 2, 4, 5]
def baseStart_473013 : Nat := 118140960795 + 473013 * 2 ^ 59
def prefixEnd_473013 : Nat := 4983230072969 + 3 ^ 40 * 473013 * 2
def baseEnd_473013 : Nat := 35982670344483417505505

theorem tailTrace_473013 : CollatzResearch.WordTrace tailWord_473013 prefixEnd_473013 35982670344483417505505 := by
  unfold tailWord_473013
  simp only [CollatzResearch.WordTrace]
  refine ⟨17252201435362160033951693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11501467623574773355967795 17252201435362160033951693)
  ·
    refine ⟨6469575538260810012731885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17252201435362160033951693 6469575538260810012731885)
    ·
      refine ⟨2426090826847803754774457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6469575538260810012731885 2426090826847803754774457)
      ·
        refine ⟨1819568120135852816080843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2426090826847803754774457 1819568120135852816080843)
        ·
          refine ⟨2729352180203779224121265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1819568120135852816080843 2729352180203779224121265)
          ·
            refine ⟨2047014135152834418090949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2729352180203779224121265 2047014135152834418090949)
            ·
              refine ⟨383815150341156453392053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2047014135152834418090949 383815150341156453392053)
              ·
                refine ⟨35982670344483417505505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 383815150341156453392053 35982670344483417505505)
                ·
                  rfl

theorem cell21_473013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 5].length) (baseStart_473013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_473013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_473013 prefixEnd_473013 := by exact prefixLift 473013
  have htrace : WordTrace (prefixWord ++ tailWord_473013) baseStart_473013 baseEnd_473013 := by
    simpa [prefixWord, tailWord_473013, baseEnd_473013] using wordTrace_append hprefix tailTrace_473013
  have hstable : (prefixWord ++ tailWord_473013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473013).length < 2 ^ (prefixWord ++ tailWord_473013).sum := by decide
  have hdescent : baseEnd_473013 < baseStart_473013 := by decide
  rcases family_descends (prefixWord ++ tailWord_473013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473092 : List Nat := [2, 3, 2, 4, 1, 1, 2, 2, 4]
def baseStart_473092 : Nat := 118140960795 + 473092 * 2 ^ 59
def prefixEnd_473092 : Nat := 4983230072969 + 3 ^ 40 * 473092 * 2
def baseEnd_473092 : Nat := 107966039909763670699687

theorem tailTrace_473092 : CollatzResearch.WordTrace tailWord_473092 prefixEnd_473092 107966039909763670699687 := by
  unfold tailWord_473092
  simp only [CollatzResearch.WordTrace]
  refine ⟨8627541401037978263038765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11503388534717304350718353 8627541401037978263038765)
  ·
    refine ⟨3235328025389241848639537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8627541401037978263038765 3235328025389241848639537)
    ·
      refine ⟨2426496019041931386479653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3235328025389241848639537 2426496019041931386479653)
      ·
        refine ⟨454968003570362134964935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2426496019041931386479653 454968003570362134964935)
        ·
          refine ⟨682452005355543202447403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454968003570362134964935 682452005355543202447403)
          ·
            refine ⟨1023678008033314803671105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682452005355543202447403 1023678008033314803671105)
            ·
              refine ⟨767758506024986102753329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1023678008033314803671105 767758506024986102753329)
              ·
                refine ⟨575818879518739577064997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 767758506024986102753329 575818879518739577064997)
                ·
                  refine ⟨107966039909763670699687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 575818879518739577064997 107966039909763670699687)
                  ·
                    rfl

theorem cell21_473092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_473092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_473092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_473092 prefixEnd_473092 := by exact prefixLift 473092
  have htrace : WordTrace (prefixWord ++ tailWord_473092) baseStart_473092 baseEnd_473092 := by
    simpa [prefixWord, tailWord_473092, baseEnd_473092] using wordTrace_append hprefix tailTrace_473092
  have hstable : (prefixWord ++ tailWord_473092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473092).length < 2 ^ (prefixWord ++ tailWord_473092).sum := by decide
  have hdescent : baseEnd_473092 < baseStart_473092 := by decide
  rcases family_descends (prefixWord ++ tailWord_473092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473196 : List Nat := [2, 2, 1, 1, 3, 3, 3, 3, 3]
def baseStart_473196 : Nat := 118140960795 + 473196 * 2 ^ 59
def prefixEnd_473196 : Nat := 4983230072969 + 3 ^ 40 * 473196 * 2
def baseEnd_473196 : Nat := 107989774126682600966141

theorem tailTrace_473196 : CollatzResearch.WordTrace tailWord_473196 prefixEnd_473196 107989774126682600966141 := by
  unfold tailWord_473196
  simp only [CollatzResearch.WordTrace]
  refine ⟨8629437996849591143931721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11505917329132788191908961 8629437996849591143931721)
  ·
    refine ⟨6472078497637193357948791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8629437996849591143931721 6472078497637193357948791)
    ·
      refine ⟨9708117746455790036923187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6472078497637193357948791 9708117746455790036923187)
      ·
        refine ⟨14562176619683685055384781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9708117746455790036923187 14562176619683685055384781)
        ·
          refine ⟨5460816232381381895769293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14562176619683685055384781 5460816232381381895769293)
          ·
            refine ⟨2047806087143018210913485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5460816232381381895769293 2047806087143018210913485)
            ·
              refine ⟨767927282678631829092557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2047806087143018210913485 767927282678631829092557)
              ·
                refine ⟨287972731004486935909709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 767927282678631829092557 287972731004486935909709)
                ·
                  refine ⟨107989774126682600966141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 287972731004486935909709 107989774126682600966141)
                  ·
                    rfl

theorem cell21_473196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3, 3].length) (baseStart_473196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_473196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_473196 prefixEnd_473196 := by exact prefixLift 473196
  have htrace : WordTrace (prefixWord ++ tailWord_473196) baseStart_473196 baseEnd_473196 := by
    simpa [prefixWord, tailWord_473196, baseEnd_473196] using wordTrace_append hprefix tailTrace_473196
  have hstable : (prefixWord ++ tailWord_473196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473196).length < 2 ^ (prefixWord ++ tailWord_473196).sum := by decide
  have hdescent : baseEnd_473196 < baseStart_473196 := by decide
  rcases family_descends (prefixWord ++ tailWord_473196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473207 : List Nat := [1, 1, 3, 1, 1, 5, 9]
def baseStart_473207 : Nat := 118140960795 + 473207 * 2 ^ 59
def prefixEnd_473207 : Nat := 4983230072969 + 3 ^ 40 * 473207 * 2
def baseEnd_473207 : Nat := 11999142719616558475865

theorem tailTrace_473207 : CollatzResearch.WordTrace tailWord_473207 prefixEnd_473207 11999142719616558475865 := by
  unfold tailWord_473207
  simp only [CollatzResearch.WordTrace]
  refine ⟨17259277196659331166513875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11506184797772887444342583 17259277196659331166513875)
  ·
    refine ⟨25888915794988996749770813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17259277196659331166513875 25888915794988996749770813)
    ·
      refine ⟨9708343423120873781164055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25888915794988996749770813 9708343423120873781164055)
      ·
        refine ⟨14562515134681310671746083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9708343423120873781164055 14562515134681310671746083)
        ·
          refine ⟨21843772702021966007619125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14562515134681310671746083 21843772702021966007619125)
          ·
            refine ⟨2047853690814559313214293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21843772702021966007619125 2047853690814559313214293)
            ·
              refine ⟨11999142719616558475865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2047853690814559313214293 11999142719616558475865)
              ·
                rfl

theorem cell21_473207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 9].length) (baseStart_473207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_473207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_473207 prefixEnd_473207 := by exact prefixLift 473207
  have htrace : WordTrace (prefixWord ++ tailWord_473207) baseStart_473207 baseEnd_473207 := by
    simpa [prefixWord, tailWord_473207, baseEnd_473207] using wordTrace_append hprefix tailTrace_473207
  have hstable : (prefixWord ++ tailWord_473207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473207).length < 2 ^ (prefixWord ++ tailWord_473207).sum := by decide
  have hdescent : baseEnd_473207 < baseStart_473207 := by decide
  rcases family_descends (prefixWord ++ tailWord_473207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473213 : List Nat := [1, 4, 1, 1, 3, 3, 3, 2, 3]
def baseStart_473213 : Nat := 118140960795 + 473213 * 2 ^ 59
def prefixEnd_473213 : Nat := 4983230072969 + 3 ^ 40 * 473213 * 2
def baseEnd_473213 : Nat := 107993653758294349182773

theorem tailTrace_473213 : CollatzResearch.WordTrace tailWord_473213 prefixEnd_473213 107993653758294349182773 := by
  unfold tailWord_473213
  simp only [CollatzResearch.WordTrace]
  refine ⟨17259496034637594191232293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11506330689758396127488195 17259496034637594191232293)
  ·
    refine ⟨3236155506494548910856055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17259496034637594191232293 3236155506494548910856055)
    ·
      refine ⟨4854233259741823366284083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3236155506494548910856055 4854233259741823366284083)
      ·
        refine ⟨7281349889612735049426125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4854233259741823366284083 7281349889612735049426125)
        ·
          refine ⟨2730506208604775643534797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7281349889612735049426125 2730506208604775643534797)
          ·
            refine ⟨1023939828226790866325549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2730506208604775643534797 1023939828226790866325549)
            ·
              refine ⟨383977435585046574872081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1023939828226790866325549 383977435585046574872081)
              ·
                refine ⟨287983076688784931154061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 383977435585046574872081 287983076688784931154061)
                ·
                  refine ⟨107993653758294349182773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 287983076688784931154061 107993653758294349182773)
                  ·
                    rfl

theorem cell21_473213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_473213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_473213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_473213 prefixEnd_473213 := by exact prefixLift 473213
  have htrace : WordTrace (prefixWord ++ tailWord_473213) baseStart_473213 baseEnd_473213 := by
    simpa [prefixWord, tailWord_473213, baseEnd_473213] using wordTrace_append hprefix tailTrace_473213
  have hstable : (prefixWord ++ tailWord_473213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473213).length < 2 ^ (prefixWord ++ tailWord_473213).sum := by decide
  have hdescent : baseEnd_473213 < baseStart_473213 := by decide
  rcases family_descends (prefixWord ++ tailWord_473213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473224 : List Nat := [2, 1, 3, 4, 1, 1, 1, 8]
def baseStart_473224 : Nat := 118140960795 + 473224 * 2 ^ 59
def prefixEnd_473224 : Nat := 4983230072969 + 3 ^ 40 * 473224 * 2
def baseEnd_473224 : Nat := 35998721369386924833139

theorem tailTrace_473224 : CollatzResearch.WordTrace tailWord_473224 prefixEnd_473224 35998721369386924833139 := by
  unfold tailWord_473224
  simp only [CollatzResearch.WordTrace]
  refine ⟨8629948618798871534941363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11506598158398495379921817 8629948618798871534941363)
  ·
    refine ⟨12944922928198307302412045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8629948618798871534941363 12944922928198307302412045)
    ·
      refine ⟨4854346098074365238404517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12944922928198307302412045 4854346098074365238404517)
      ·
        refine ⟨910189893388943482200847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4854346098074365238404517 910189893388943482200847)
        ·
          refine ⟨1365284840083415223301271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 910189893388943482200847 1365284840083415223301271)
          ·
            refine ⟨2047927260125122834951907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1365284840083415223301271 2047927260125122834951907)
            ·
              refine ⟨3071890890187684252427861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2047927260125122834951907 3071890890187684252427861)
              ·
                refine ⟨35998721369386924833139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3071890890187684252427861 35998721369386924833139)
                ·
                  rfl

theorem cell21_473224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 8].length) (baseStart_473224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_473224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_473224 prefixEnd_473224 := by exact prefixLift 473224
  have htrace : WordTrace (prefixWord ++ tailWord_473224) baseStart_473224 baseEnd_473224 := by
    simpa [prefixWord, tailWord_473224, baseEnd_473224] using wordTrace_append hprefix tailTrace_473224
  have hstable : (prefixWord ++ tailWord_473224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473224).length < 2 ^ (prefixWord ++ tailWord_473224).sum := by decide
  have hdescent : baseEnd_473224 < baseStart_473224 := by decide
  rcases family_descends (prefixWord ++ tailWord_473224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473331 : List Nat := [1, 1, 1, 2, 2, 4, 1, 6, 3]
def baseStart_473331 : Nat := 118140960795 + 473331 * 2 ^ 59
def prefixEnd_473331 : Nat := 4983230072969 + 3 ^ 40 * 473331 * 2
def baseEnd_473331 : Nat := 108020582965952366215865

theorem tailTrace_473331 : CollatzResearch.WordTrace tailWord_473331 prefixEnd_473331 108020582965952366215865 := by
  unfold tailWord_473331
  simp only [CollatzResearch.WordTrace]
  refine ⟨17263799848210100344027847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11509199898806733562685231 17263799848210100344027847)
  ·
    refine ⟨25895699772315150516041771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17263799848210100344027847 25895699772315150516041771)
    ·
      refine ⟨38843549658472725774062657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25895699772315150516041771 38843549658472725774062657)
      ·
        refine ⟨29132662243854544330546993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38843549658472725774062657 29132662243854544330546993)
        ·
          refine ⟨21849496682890908247910245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29132662243854544330546993 21849496682890908247910245)
          ·
            refine ⟨4096780628042045296483171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21849496682890908247910245 4096780628042045296483171)
            ·
              refine ⟨6145170942063067944724757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4096780628042045296483171 6145170942063067944724757)
              ·
                refine ⟨288054887909206309908973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6145170942063067944724757 288054887909206309908973)
                ·
                  refine ⟨108020582965952366215865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 288054887909206309908973 108020582965952366215865)
                  ·
                    rfl

theorem cell21_473331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 6, 3].length) (baseStart_473331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_473331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_473331 prefixEnd_473331 := by exact prefixLift 473331
  have htrace : WordTrace (prefixWord ++ tailWord_473331) baseStart_473331 baseEnd_473331 := by
    simpa [prefixWord, tailWord_473331, baseEnd_473331] using wordTrace_append hprefix tailTrace_473331
  have hstable : (prefixWord ++ tailWord_473331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473331).length < 2 ^ (prefixWord ++ tailWord_473331).sum := by decide
  have hdescent : baseEnd_473331 < baseStart_473331 := by decide
  rcases family_descends (prefixWord ++ tailWord_473331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473351 : List Nat := [1, 1, 4, 5, 2, 1, 2, 5]
def baseStart_473351 : Nat := 118140960795 + 473351 * 2 ^ 59
def prefixEnd_473351 : Nat := 4983230072969 + 3 ^ 40 * 473351 * 2
def baseEnd_473351 : Nat := 36008382412812258627497

theorem tailTrace_473351 : CollatzResearch.WordTrace tailWord_473351 prefixEnd_473351 36008382412812258627497 := by
  unfold tailWord_473351
  simp only [CollatzResearch.WordTrace]
  refine ⟨17264529308137643759755907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11509686205425095839837271 17264529308137643759755907)
  ·
    refine ⟨25896793962206465639633861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17264529308137643759755907 25896793962206465639633861)
    ·
      refine ⟨4855648867913712307431349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25896793962206465639633861 4855648867913712307431349)
      ·
        refine ⟨455217081366910528821689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4855648867913712307431349 455217081366910528821689)
        ·
          refine ⟨341412811025182896616267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455217081366910528821689 341412811025182896616267)
          ·
            refine ⟨512119216537774344924401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341412811025182896616267 512119216537774344924401)
            ·
              refine ⟨384089412403330758693301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 512119216537774344924401 384089412403330758693301)
              ·
                refine ⟨36008382412812258627497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 384089412403330758693301 36008382412812258627497)
                ·
                  rfl

theorem cell21_473351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 5].length) (baseStart_473351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_473351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_473351 prefixEnd_473351 := by exact prefixLift 473351
  have htrace : WordTrace (prefixWord ++ tailWord_473351) baseStart_473351 baseEnd_473351 := by
    simpa [prefixWord, tailWord_473351, baseEnd_473351] using wordTrace_append hprefix tailTrace_473351
  have hstable : (prefixWord ++ tailWord_473351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473351).length < 2 ^ (prefixWord ++ tailWord_473351).sum := by decide
  have hdescent : baseEnd_473351 < baseStart_473351 := by decide
  rcases family_descends (prefixWord ++ tailWord_473351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473376 : List Nat := [2, 1, 1, 5, 2, 3, 7]
def baseStart_473376 : Nat := 118140960795 + 473376 * 2 ^ 59
def prefixEnd_473376 : Nat := 4983230072969 + 3 ^ 40 * 473376 * 2
def baseEnd_473376 : Nat := 12003428064338031996197

theorem tailTrace_473376 : CollatzResearch.WordTrace tailWord_473376 prefixEnd_473376 12003428064338031996197 := by
  unfold tailWord_473376
  simp only [CollatzResearch.WordTrace]
  refine ⟨8632720566523536514707991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11510294088698048686277321 8632720566523536514707991)
  ·
    refine ⟨12949080849785304772061987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8632720566523536514707991 12949080849785304772061987)
    ·
      refine ⟨19423621274677957158092981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12949080849785304772061987 19423621274677957158092981)
      ·
        refine ⟨1820964494501058483571217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19423621274677957158092981 1820964494501058483571217)
        ·
          refine ⟨1365723370875793862678413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1820964494501058483571217 1365723370875793862678413)
          ·
            refine ⟨512146264078422698504405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1365723370875793862678413 512146264078422698504405)
            ·
              refine ⟨12003428064338031996197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 512146264078422698504405 12003428064338031996197)
              ·
                rfl

theorem cell21_473376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 7].length) (baseStart_473376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_473376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_473376 prefixEnd_473376 := by exact prefixLift 473376
  have htrace : WordTrace (prefixWord ++ tailWord_473376) baseStart_473376 baseEnd_473376 := by
    simpa [prefixWord, tailWord_473376, baseEnd_473376] using wordTrace_append hprefix tailTrace_473376
  have hstable : (prefixWord ++ tailWord_473376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473376).length < 2 ^ (prefixWord ++ tailWord_473376).sum := by decide
  have hdescent : baseEnd_473376 < baseStart_473376 := by decide
  rcases family_descends (prefixWord ++ tailWord_473376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473396 : List Nat := [2, 5, 1, 1, 1, 4, 2, 1, 4]
def baseStart_473396 : Nat := 118140960795 + 473396 * 2 ^ 59
def prefixEnd_473396 : Nat := 4983230072969 + 3 ^ 40 * 473396 * 2
def baseEnd_473396 : Nat := 108035416851526697632399

theorem tailTrace_473396 : CollatzResearch.WordTrace tailWord_473396 prefixEnd_473396 108035416851526697632399 := by
  unfold tailWord_473396
  simp only [CollatzResearch.WordTrace]
  refine ⟨8633085296487308222572021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11510780395316410963429361 8633085296487308222572021)
  ·
    refine ⟨809351746545685145866127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8633085296487308222572021 809351746545685145866127)
    ·
      refine ⟨1214027619818527718799191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 809351746545685145866127 1214027619818527718799191)
      ·
        refine ⟨1821041429727791578198787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1214027619818527718799191 1821041429727791578198787)
        ·
          refine ⟨2731562144591687367298181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1821041429727791578198787 2731562144591687367298181)
          ·
            refine ⟨512167902110941381368409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2731562144591687367298181 512167902110941381368409)
            ·
              refine ⟨384125926583206036026307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 512167902110941381368409 384125926583206036026307)
              ·
                refine ⟨576188889874809054039461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384125926583206036026307 576188889874809054039461)
                ·
                  refine ⟨108035416851526697632399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 576188889874809054039461 108035416851526697632399)
                  ·
                    rfl

theorem cell21_473396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_473396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_473396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_473396 prefixEnd_473396 := by exact prefixLift 473396
  have htrace : WordTrace (prefixWord ++ tailWord_473396) baseStart_473396 baseEnd_473396 := by
    simpa [prefixWord, tailWord_473396, baseEnd_473396] using wordTrace_append hprefix tailTrace_473396
  have hstable : (prefixWord ++ tailWord_473396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473396).length < 2 ^ (prefixWord ++ tailWord_473396).sum := by decide
  have hdescent : baseEnd_473396 < baseStart_473396 := by decide
  rcases family_descends (prefixWord ++ tailWord_473396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473483 : List Nat := [1, 1, 1, 1, 4, 4, 1, 5, 3]
def baseStart_473483 : Nat := 118140960795 + 473483 * 2 ^ 59
def prefixEnd_473483 : Nat := 4983230072969 + 3 ^ 40 * 473483 * 2
def baseEnd_473483 : Nat := 108055271436833879682221

theorem tailTrace_473483 : CollatzResearch.WordTrace tailWord_473483 prefixEnd_473483 108055271436833879682221 := by
  unfold tailWord_473483
  simp only [CollatzResearch.WordTrace]
  refine ⟨17269343743659430303561103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11512895829106286869040735 17269343743659430303561103)
  ·
    refine ⟨25904015615489145455341655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17269343743659430303561103 25904015615489145455341655)
    ·
      refine ⟨38856023423233718183012483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25904015615489145455341655 38856023423233718183012483)
      ·
        refine ⟨58284035134850577274518725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38856023423233718183012483 58284035134850577274518725)
        ·
          refine ⟨10928256587784483238972261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58284035134850577274518725 10928256587784483238972261)
          ·
            refine ⟨2049048110209590607307299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10928256587784483238972261 2049048110209590607307299)
            ·
              refine ⟨3073572165314385910960949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2049048110209590607307299 3073572165314385910960949)
              ·
                refine ⟨288147390498223679152589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3073572165314385910960949 288147390498223679152589)
                ·
                  refine ⟨108055271436833879682221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 288147390498223679152589 108055271436833879682221)
                  ·
                    rfl

theorem cell21_473483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 5, 3].length) (baseStart_473483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_473483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_473483 prefixEnd_473483 := by exact prefixLift 473483
  have htrace : WordTrace (prefixWord ++ tailWord_473483) baseStart_473483 baseEnd_473483 := by
    simpa [prefixWord, tailWord_473483, baseEnd_473483] using wordTrace_append hprefix tailTrace_473483
  have hstable : (prefixWord ++ tailWord_473483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473483).length < 2 ^ (prefixWord ++ tailWord_473483).sum := by decide
  have hdescent : baseEnd_473483 < baseStart_473483 := by decide
  rcases family_descends (prefixWord ++ tailWord_473483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473708 : List Nat := [2, 2, 1, 1, 3, 1, 3, 2, 6]
def baseStart_473708 : Nat := 118140960795 + 473708 * 2 ^ 59
def prefixEnd_473708 : Nat := 4983230072969 + 3 ^ 40 * 473708 * 2
def baseEnd_473708 : Nat := 108106619502283488431761

theorem tailTrace_473708 : CollatzResearch.WordTrace tailWord_473708 prefixEnd_473708 108106619502283488431761 := by
  unfold tailWord_473708
  simp only [CollatzResearch.WordTrace]
  refine ⟨8638775083922146865250889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11518366778562862487001185 8638775083922146865250889)
  ·
    refine ⟨6479081312941610148938167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8638775083922146865250889 6479081312941610148938167)
    ·
      refine ⟨9718621969412415223407251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6479081312941610148938167 9718621969412415223407251)
      ·
        refine ⟨14577932954118622835110877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9718621969412415223407251 14577932954118622835110877)
        ·
          refine ⟨5466724857794483563166579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14577932954118622835110877 5466724857794483563166579)
          ·
            refine ⟨8200087286691725344749869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5466724857794483563166579 8200087286691725344749869)
            ·
              refine ⟨3075032732509397004281201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8200087286691725344749869 3075032732509397004281201)
              ·
                refine ⟨2306274549382047753210901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3075032732509397004281201 2306274549382047753210901)
                ·
                  refine ⟨108106619502283488431761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2306274549382047753210901 108106619502283488431761)
                  ·
                    rfl

theorem cell21_473708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_473708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_473708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_473708 prefixEnd_473708 := by exact prefixLift 473708
  have htrace : WordTrace (prefixWord ++ tailWord_473708) baseStart_473708 baseEnd_473708 := by
    simpa [prefixWord, tailWord_473708, baseEnd_473708] using wordTrace_append hprefix tailTrace_473708
  have hstable : (prefixWord ++ tailWord_473708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473708).length < 2 ^ (prefixWord ++ tailWord_473708).sum := by decide
  have hdescent : baseEnd_473708 < baseStart_473708 := by decide
  rcases family_descends (prefixWord ++ tailWord_473708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473711 : List Nat := [1, 1, 2, 1, 3, 2, 5, 3, 3]
def baseStart_473711 : Nat := 118140960795 + 473711 * 2 ^ 59
def prefixEnd_473711 : Nat := 4983230072969 + 3 ^ 40 * 473711 * 2
def baseEnd_473711 : Nat := 108107304143156149881755

theorem tailTrace_473711 : CollatzResearch.WordTrace tailWord_473711 prefixEnd_473711 108107304143156149881755 := by
  unfold tailWord_473711
  simp only [CollatzResearch.WordTrace]
  refine ⟨17277659586833425242860987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11518439724555616828573991 17277659586833425242860987)
  ·
    refine ⟨25916489380250137864291481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17277659586833425242860987 25916489380250137864291481)
    ·
      refine ⟨19437367035187603398218611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25916489380250137864291481 19437367035187603398218611)
      ·
        refine ⟨29156050552781405097327917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19437367035187603398218611 29156050552781405097327917)
        ·
          refine ⟨10933518957293026911497969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29156050552781405097327917 10933518957293026911497969)
          ·
            refine ⟨8200139217969770183623477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10933518957293026911497969 8200139217969770183623477)
            ·
              refine ⟨768763051684665954714701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8200139217969770183623477 768763051684665954714701)
              ·
                refine ⟨288286144381749733018013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 768763051684665954714701 288286144381749733018013)
                ·
                  refine ⟨108107304143156149881755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 288286144381749733018013 108107304143156149881755)
                  ·
                    rfl

theorem cell21_473711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 3, 3].length) (baseStart_473711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_473711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_473711 prefixEnd_473711 := by exact prefixLift 473711
  have htrace : WordTrace (prefixWord ++ tailWord_473711) baseStart_473711 baseEnd_473711 := by
    simpa [prefixWord, tailWord_473711, baseEnd_473711] using wordTrace_append hprefix tailTrace_473711
  have hstable : (prefixWord ++ tailWord_473711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473711).length < 2 ^ (prefixWord ++ tailWord_473711).sum := by decide
  have hdescent : baseEnd_473711 < baseStart_473711 := by decide
  rcases family_descends (prefixWord ++ tailWord_473711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473728 : List Nat := [2, 1, 1, 2, 1, 6, 3, 2, 3]
def baseStart_473728 : Nat := 118140960795 + 473728 * 2 ^ 59
def prefixEnd_473728 : Nat := 4983230072969 + 3 ^ 40 * 473728 * 2
def baseEnd_473728 : Nat := 108111183774767898098387

theorem tailTrace_473728 : CollatzResearch.WordTrace tailWord_473728 prefixEnd_473728 108111183774767898098387 := by
  unfold tailWord_473728
  simp only [CollatzResearch.WordTrace]
  refine ⟨8639139813885918573114919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11518853085181224764153225 8639139813885918573114919)
  ·
    refine ⟨12958709720828877859672379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8639139813885918573114919 12958709720828877859672379)
    ·
      refine ⟨19438064581243316789508569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12958709720828877859672379 19438064581243316789508569)
      ·
        refine ⟨14578548435932487592131427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19438064581243316789508569 14578548435932487592131427)
        ·
          refine ⟨21867822653898731388197141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14578548435932487592131427 21867822653898731388197141)
          ·
            refine ⟨1025054186901503033821741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21867822653898731388197141 1025054186901503033821741)
            ·
              refine ⟨384395320088063637683153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1025054186901503033821741 384395320088063637683153)
              ·
                refine ⟨288296490066047728262365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 384395320088063637683153 288296490066047728262365)
                ·
                  refine ⟨108111183774767898098387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 288296490066047728262365 108111183774767898098387)
                  ·
                    rfl

theorem cell21_473728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 2, 3].length) (baseStart_473728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_473728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_473728 prefixEnd_473728 := by exact prefixLift 473728
  have htrace : WordTrace (prefixWord ++ tailWord_473728) baseStart_473728 baseEnd_473728 := by
    simpa [prefixWord, tailWord_473728, baseEnd_473728] using wordTrace_append hprefix tailTrace_473728
  have hstable : (prefixWord ++ tailWord_473728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473728).length < 2 ^ (prefixWord ++ tailWord_473728).sum := by decide
  have hdescent : baseEnd_473728 < baseStart_473728 := by decide
  rcases family_descends (prefixWord ++ tailWord_473728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473753 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 7]
def baseStart_473753 : Nat := 118140960795 + 473753 * 2 ^ 59
def prefixEnd_473753 : Nat := 4983230072969 + 3 ^ 40 * 473753 * 2
def baseEnd_473753 : Nat := 108116889115373410181669

theorem tailTrace_473753 : CollatzResearch.WordTrace tailWord_473753 prefixEnd_473753 108116889115373410181669 := by
  unfold tailWord_473753
  simp only [CollatzResearch.WordTrace]
  refine ⟨17279191452681266415889913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11519460968454177610593275 17279191452681266415889913)
  ·
    refine ⟨12959393589510949811917435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17279191452681266415889913 12959393589510949811917435)
    ·
      refine ⟨19439090384266424717876153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12959393589510949811917435 19439090384266424717876153)
      ·
        refine ⟨14579317788199818538407115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19439090384266424717876153 14579317788199818538407115)
        ·
          refine ⟨21868976682299727807610673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14579317788199818538407115 21868976682299727807610673)
          ·
            refine ⟨16401732511724795855708005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21868976682299727807610673 16401732511724795855708005)
            ·
              refine ⟨3075324845948399222945251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16401732511724795855708005 3075324845948399222945251)
              ·
                refine ⟨4612987268922598834417877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3075324845948399222945251 4612987268922598834417877)
                ·
                  refine ⟨108116889115373410181669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4612987268922598834417877 108116889115373410181669)
                  ·
                    rfl

theorem cell21_473753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 7].length) (baseStart_473753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_473753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_473753 prefixEnd_473753 := by exact prefixLift 473753
  have htrace : WordTrace (prefixWord ++ tailWord_473753) baseStart_473753 baseEnd_473753 := by
    simpa [prefixWord, tailWord_473753, baseEnd_473753] using wordTrace_append hprefix tailTrace_473753
  have hstable : (prefixWord ++ tailWord_473753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473753).length < 2 ^ (prefixWord ++ tailWord_473753).sum := by decide
  have hdescent : baseEnd_473753 < baseStart_473753 := by decide
  rcases family_descends (prefixWord ++ tailWord_473753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473956 : List Nat := [2, 3, 1, 1, 4, 1, 4, 2, 3]
def baseStart_473956 : Nat := 118140960795 + 473956 * 2 ^ 59
def prefixEnd_473956 : Nat := 4983230072969 + 3 ^ 40 * 473956 * 2
def baseEnd_473956 : Nat := 108163216481090168297921

theorem tailTrace_473956 : CollatzResearch.WordTrace tailWord_473956 prefixEnd_473956 108163216481090168297921 := by
  unfold tailWord_473956
  simp only [CollatzResearch.WordTrace]
  refine ⟨8643297735472916042764861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11524396980630554723686481 8643297735472916042764861)
  ·
    refine ⟨3241236650802343516036823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8643297735472916042764861 3241236650802343516036823)
    ·
      refine ⟨4861854976203515274055235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3241236650802343516036823 4861854976203515274055235)
      ·
        refine ⟨7292782464305272911082853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4861854976203515274055235 7292782464305272911082853)
        ·
          refine ⟨1367396712057238670828035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7292782464305272911082853 1367396712057238670828035)
          ·
            refine ⟨2051095068085858006242053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1367396712057238670828035 2051095068085858006242053)
            ·
              refine ⟨384580325266098376170385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2051095068085858006242053 384580325266098376170385)
              ·
                refine ⟨288435243949573782127789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 384580325266098376170385 288435243949573782127789)
                ·
                  refine ⟨108163216481090168297921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 288435243949573782127789 108163216481090168297921)
                  ·
                    rfl

theorem cell21_473956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_473956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_473956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_473956 prefixEnd_473956 := by exact prefixLift 473956
  have htrace : WordTrace (prefixWord ++ tailWord_473956) baseStart_473956 baseEnd_473956 := by
    simpa [prefixWord, tailWord_473956, baseEnd_473956] using wordTrace_append hprefix tailTrace_473956
  have hstable : (prefixWord ++ tailWord_473956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473956).length < 2 ^ (prefixWord ++ tailWord_473956).sum := by decide
  have hdescent : baseEnd_473956 < baseStart_473956 := by decide
  rcases family_descends (prefixWord ++ tailWord_473956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473981 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 7]
def baseStart_473981 : Nat := 118140960795 + 473981 * 2 ^ 59
def prefixEnd_473981 : Nat := 4983230072969 + 3 ^ 40 * 473981 * 2
def baseEnd_473981 : Nat := 108168921821695680381203

theorem tailTrace_473981 : CollatzResearch.WordTrace tailWord_473981 prefixEnd_473981 108168921821695680381203 := by
  unfold tailWord_473981
  simp only [CollatzResearch.WordTrace]
  refine ⟨17287507295855261355189797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11525004863903507570126531 17287507295855261355189797)
  ·
    refine ⟨3241407617972861504098087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17287507295855261355189797 3241407617972861504098087)
    ·
      refine ⟨4862111426959292256147131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3241407617972861504098087 4862111426959292256147131)
      ·
        refine ⟨7293167140438938384220697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4862111426959292256147131 7293167140438938384220697)
        ·
          refine ⟨5469875355329203788165523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7293167140438938384220697 5469875355329203788165523)
          ·
            refine ⟨8204813032993805682248285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5469875355329203788165523 8204813032993805682248285)
            ·
              refine ⟨3076804887372677130843107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8204813032993805682248285 3076804887372677130843107)
              ·
                refine ⟨4615207331059015696264661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3076804887372677130843107 4615207331059015696264661)
                ·
                  refine ⟨108168921821695680381203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4615207331059015696264661 108168921821695680381203)
                  ·
                    rfl

theorem cell21_473981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_473981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_473981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_473981 prefixEnd_473981 := by exact prefixLift 473981
  have htrace : WordTrace (prefixWord ++ tailWord_473981) baseStart_473981 baseEnd_473981 := by
    simpa [prefixWord, tailWord_473981, baseEnd_473981] using wordTrace_append hprefix tailTrace_473981
  have hstable : (prefixWord ++ tailWord_473981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473981).length < 2 ^ (prefixWord ++ tailWord_473981).sum := by decide
  have hdescent : baseEnd_473981 < baseStart_473981 := by decide
  rcases family_descends (prefixWord ++ tailWord_473981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474015 : List Nat := [1, 1, 2, 5, 2, 1, 2, 4, 3]
def baseStart_474015 : Nat := 118140960795 + 474015 * 2 ^ 59
def prefixEnd_474015 : Nat := 4983230072969 + 3 ^ 40 * 474015 * 2
def baseEnd_474015 : Nat := 108176681084919176814467

theorem tailTrace_474015 : CollatzResearch.WordTrace tailWord_474015 prefixEnd_474015 108176681084919176814467 := by
  unfold tailWord_474015
  simp only [CollatzResearch.WordTrace]
  refine ⟨17288747377732085161927499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11525831585154723441284999 17288747377732085161927499)
  ·
    refine ⟨25933121066598127742891249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17288747377732085161927499 25933121066598127742891249)
    ·
      refine ⟨19449840799948595807168437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25933121066598127742891249 19449840799948595807168437)
      ·
        refine ⟨1823422574995180856922041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19449840799948595807168437 1823422574995180856922041)
        ·
          refine ⟨1367566931246385642691531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1823422574995180856922041 1367566931246385642691531)
          ·
            refine ⟨2051350396869578464037297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1367566931246385642691531 2051350396869578464037297)
            ·
              refine ⟨1538512797652183848027973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2051350396869578464037297 1538512797652183848027973)
              ·
                refine ⟨288471149559784471505245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1538512797652183848027973 288471149559784471505245)
                ·
                  refine ⟨108176681084919176814467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 288471149559784471505245 108176681084919176814467)
                  ·
                    rfl

theorem cell21_474015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 4, 3].length) (baseStart_474015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_474015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_474015 prefixEnd_474015 := by exact prefixLift 474015
  have htrace : WordTrace (prefixWord ++ tailWord_474015) baseStart_474015 baseEnd_474015 := by
    simpa [prefixWord, tailWord_474015, baseEnd_474015] using wordTrace_append hprefix tailTrace_474015
  have hstable : (prefixWord ++ tailWord_474015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474015).length < 2 ^ (prefixWord ++ tailWord_474015).sum := by decide
  have hdescent : baseEnd_474015 < baseStart_474015 := by decide
  rcases family_descends (prefixWord ++ tailWord_474015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474074 : List Nat := [3, 1, 1, 2, 4, 1, 3, 1, 5]
def baseStart_474074 : Nat := 118140960795 + 474074 * 2 ^ 59
def prefixEnd_474074 : Nat := 4983230072969 + 3 ^ 40 * 474074 * 2
def baseEnd_474074 : Nat := 108190145688748185331013

theorem tailTrace_474074 : CollatzResearch.WordTrace tailWord_474074 prefixEnd_474074 108190145688748185331013 := by
  unfold tailWord_474074
  simp only [CollatzResearch.WordTrace]
  refine ⟨4322724821129584559581319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11527266189678892158883517 4322724821129584559581319)
  ·
    refine ⟨6484087231694376839371979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4322724821129584559581319 6484087231694376839371979)
    ·
      refine ⟨9726130847541565259057969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6484087231694376839371979 9726130847541565259057969)
      ·
        refine ⟨7294598135656173944293477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9726130847541565259057969 7294598135656173944293477)
        ·
          refine ⟨1367737150435532614555027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7294598135656173944293477 1367737150435532614555027)
          ·
            refine ⟨2051605725653298921832541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1367737150435532614555027 2051605725653298921832541)
            ·
              refine ⟨769352147119987095687203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2051605725653298921832541 769352147119987095687203)
              ·
                refine ⟨1154028220679980643530805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 769352147119987095687203 1154028220679980643530805)
                ·
                  refine ⟨108190145688748185331013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1154028220679980643530805 108190145688748185331013)
                  ·
                    rfl

theorem cell21_474074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_474074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_474074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_474074 prefixEnd_474074 := by exact prefixLift 474074
  have htrace : WordTrace (prefixWord ++ tailWord_474074) baseStart_474074 baseEnd_474074 := by
    simpa [prefixWord, tailWord_474074, baseEnd_474074] using wordTrace_append hprefix tailTrace_474074
  have hstable : (prefixWord ++ tailWord_474074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474074).length < 2 ^ (prefixWord ++ tailWord_474074).sum := by decide
  have hdescent : baseEnd_474074 < baseStart_474074 := by decide
  rcases family_descends (prefixWord ++ tailWord_474074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474209 : List Nat := [1, 2, 3, 1, 1, 2, 4, 2, 5]
def baseStart_474209 : Nat := 118140960795 + 474209 * 2 ^ 59
def prefixEnd_474209 : Nat := 4983230072969 + 3 ^ 40 * 474209 * 2
def baseEnd_474209 : Nat := 108220954528017950580737

theorem tailTrace_474209 : CollatzResearch.WordTrace tailWord_474209 prefixEnd_474209 108220954528017950580737 := by
  unfold tailWord_474209
  simp only [CollatzResearch.WordTrace]
  refine ⟨17295823139029256294489681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11530548759352837529659787 17295823139029256294489681)
  ·
    refine ⟨12971867354271942220867261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17295823139029256294489681 12971867354271942220867261)
    ·
      refine ⟨4864450257851978332825223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12971867354271942220867261 4864450257851978332825223)
      ·
        refine ⟨7296675386777967499237835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4864450257851978332825223 7296675386777967499237835)
        ·
          refine ⟨10945013080166951248856753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7296675386777967499237835 10945013080166951248856753)
          ·
            refine ⟨8208759810125213436642565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10945013080166951248856753 8208759810125213436642565)
            ·
              refine ⟨1539142464398477519370481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8208759810125213436642565 1539142464398477519370481)
              ·
                refine ⟨1154356848298858139527861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1539142464398477519370481 1154356848298858139527861)
                ·
                  refine ⟨108220954528017950580737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1154356848298858139527861 108220954528017950580737)
                  ·
                    rfl

theorem cell21_474209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 5].length) (baseStart_474209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_474209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_474209 prefixEnd_474209 := by exact prefixLift 474209
  have htrace : WordTrace (prefixWord ++ tailWord_474209) baseStart_474209 baseEnd_474209 := by
    simpa [prefixWord, tailWord_474209, baseEnd_474209] using wordTrace_append hprefix tailTrace_474209
  have hstable : (prefixWord ++ tailWord_474209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474209).length < 2 ^ (prefixWord ++ tailWord_474209).sum := by decide
  have hdescent : baseEnd_474209 < baseStart_474209 := by decide
  rcases family_descends (prefixWord ++ tailWord_474209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474223 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 8]
def baseStart_474223 : Nat := 118140960795 + 474223 * 2 ^ 59
def prefixEnd_474223 : Nat := 4983230072969 + 3 ^ 40 * 474223 * 2
def baseEnd_474223 : Nat := 108224149518757037347375

theorem tailTrace_474223 : CollatzResearch.WordTrace tailWord_474223 prefixEnd_474223 108224149518757037347375 := by
  unfold tailWord_474223
  simp only [CollatzResearch.WordTrace]
  refine ⟨17296333760978536685499323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11530889173985691123666215 17296333760978536685499323)
  ·
    refine ⟨25944500641467805028248985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17296333760978536685499323 25944500641467805028248985)
    ·
      refine ⟨19458375481100853771186739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25944500641467805028248985 19458375481100853771186739)
      ·
        refine ⟨29187563221651280656780109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19458375481100853771186739 29187563221651280656780109)
        ·
          refine ⟨10945336208119230246292541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29187563221651280656780109 10945336208119230246292541)
          ·
            refine ⟨4104501078044711342359703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10945336208119230246292541 4104501078044711342359703)
            ·
              refine ⟨6156751617067067013539555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4104501078044711342359703 6156751617067067013539555)
              ·
                refine ⟨9235127425600600520309333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6156751617067067013539555 9235127425600600520309333)
                ·
                  refine ⟨108224149518757037347375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9235127425600600520309333 108224149518757037347375)
                  ·
                    rfl

theorem cell21_474223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 8].length) (baseStart_474223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_474223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_474223 prefixEnd_474223 := by exact prefixLift 474223
  have htrace : WordTrace (prefixWord ++ tailWord_474223) baseStart_474223 baseEnd_474223 := by
    simpa [prefixWord, tailWord_474223, baseEnd_474223] using wordTrace_append hprefix tailTrace_474223
  have hstable : (prefixWord ++ tailWord_474223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474223).length < 2 ^ (prefixWord ++ tailWord_474223).sum := by decide
  have hdescent : baseEnd_474223 < baseStart_474223 := by decide
  rcases family_descends (prefixWord ++ tailWord_474223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474229 : List Nat := [1, 3, 4, 3, 2, 1, 7]
def baseStart_474229 : Nat := 118140960795 + 474229 * 2 ^ 59
def prefixEnd_474229 : Nat := 4983230072969 + 3 ^ 40 * 474229 * 2
def baseEnd_474229 : Nat := 12025057644500262249707

theorem tailTrace_474229 : CollatzResearch.WordTrace tailWord_474229 prefixEnd_474229 12025057644500262249707 := by
  unfold tailWord_474229
  simp only [CollatzResearch.WordTrace]
  refine ⟨17296552598956799710217741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11531035065971199806811827 17296552598956799710217741)
  ·
    refine ⟨6486207224608799891331653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17296552598956799710217741 6486207224608799891331653)
    ·
      refine ⟨1216163854614149979624685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6486207224608799891331653 1216163854614149979624685)
      ·
        refine ⟨456061445480306242359257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1216163854614149979624685 456061445480306242359257)
        ·
          refine ⟨342046084110229681769443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456061445480306242359257 342046084110229681769443)
          ·
            refine ⟨513069126165344522654165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342046084110229681769443 513069126165344522654165)
            ·
              refine ⟨12025057644500262249707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 513069126165344522654165 12025057644500262249707)
              ·
                rfl

theorem cell21_474229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 7].length) (baseStart_474229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_474229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_474229 prefixEnd_474229 := by exact prefixLift 474229
  have htrace : WordTrace (prefixWord ++ tailWord_474229) baseStart_474229 baseEnd_474229 := by
    simpa [prefixWord, tailWord_474229, baseEnd_474229] using wordTrace_append hprefix tailTrace_474229
  have hstable : (prefixWord ++ tailWord_474229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474229).length < 2 ^ (prefixWord ++ tailWord_474229).sum := by decide
  have hdescent : baseEnd_474229 < baseStart_474229 := by decide
  rcases family_descends (prefixWord ++ tailWord_474229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474243 : List Nat := [1, 1, 1, 3, 3, 2, 5, 2, 3]
def baseStart_474243 : Nat := 118140960795 + 474243 * 2 ^ 59
def prefixEnd_474243 : Nat := 4983230072969 + 3 ^ 40 * 474243 * 2
def baseEnd_474243 : Nat := 108228713791241447014001

theorem tailTrace_474243 : CollatzResearch.WordTrace tailWord_474243 prefixEnd_474243 108228713791241447014001 := by
  unfold tailWord_474243
  simp only [CollatzResearch.WordTrace]
  refine ⟨17297063220906080101227383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11531375480604053400818255 17297063220906080101227383)
  ·
    refine ⟨25945594831359120151841075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17297063220906080101227383 25945594831359120151841075)
    ·
      refine ⟨38918392247038680227761613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25945594831359120151841075 38918392247038680227761613)
      ·
        refine ⟨14594397092639505085410605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38918392247038680227761613 14594397092639505085410605)
        ·
          refine ⟨5472898909739814407028977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14594397092639505085410605 5472898909739814407028977)
          ·
            refine ⟨4104674182304860805271733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5472898909739814407028977 4104674182304860805271733)
            ·
              refine ⟨384813204591080700494225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4104674182304860805271733 384813204591080700494225)
              ·
                refine ⟨288609903443310525370669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 384813204591080700494225 288609903443310525370669)
                ·
                  refine ⟨108228713791241447014001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 288609903443310525370669 108228713791241447014001)
                  ·
                    rfl

theorem cell21_474243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 2, 3].length) (baseStart_474243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_474243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_474243 prefixEnd_474243 := by exact prefixLift 474243
  have htrace : WordTrace (prefixWord ++ tailWord_474243) baseStart_474243 baseEnd_474243 := by
    simpa [prefixWord, tailWord_474243, baseEnd_474243] using wordTrace_append hprefix tailTrace_474243
  have hstable : (prefixWord ++ tailWord_474243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474243).length < 2 ^ (prefixWord ++ tailWord_474243).sum := by decide
  have hdescent : baseEnd_474243 < baseStart_474243 := by decide
  rcases family_descends (prefixWord ++ tailWord_474243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474361 : List Nat := [1, 2, 1, 3, 1, 1, 6, 1, 5]
def baseStart_474361 : Nat := 118140960795 + 474361 * 2 ^ 59
def prefixEnd_474361 : Nat := 4983230072969 + 3 ^ 40 * 474361 * 2
def baseEnd_474361 : Nat := 108255642998899464047093

theorem tailTrace_474361 : CollatzResearch.WordTrace tailWord_474361 prefixEnd_474361 108255642998899464047093 := by
  unfold tailWord_474361
  simp only [CollatzResearch.WordTrace]
  refine ⟨17301367034478586254022937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11534244689652390836015291 17301367034478586254022937)
  ·
    refine ⟨12976025275858939690517203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17301367034478586254022937 12976025275858939690517203)
    ·
      refine ⟨19464037913788409535775805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12976025275858939690517203 19464037913788409535775805)
      ·
        refine ⟨7299014217670653575915927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19464037913788409535775805 7299014217670653575915927)
        ·
          refine ⟨10948521326505980363873891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7299014217670653575915927 10948521326505980363873891)
          ·
            refine ⟨16422781989758970545810837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10948521326505980363873891 16422781989758970545810837)
            ·
              refine ⟨769817905769951744334883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16422781989758970545810837 769817905769951744334883)
              ·
                refine ⟨1154726858654927616502325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 769817905769951744334883 1154726858654927616502325)
                ·
                  refine ⟨108255642998899464047093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1154726858654927616502325 108255642998899464047093)
                  ·
                    rfl

theorem cell21_474361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 5].length) (baseStart_474361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_474361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_474361 prefixEnd_474361 := by exact prefixLift 474361
  have htrace : WordTrace (prefixWord ++ tailWord_474361) baseStart_474361 baseEnd_474361 := by
    simpa [prefixWord, tailWord_474361, baseEnd_474361] using wordTrace_append hprefix tailTrace_474361
  have hstable : (prefixWord ++ tailWord_474361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474361).length < 2 ^ (prefixWord ++ tailWord_474361).sum := by decide
  have hdescent : baseEnd_474361 < baseStart_474361 := by decide
  rcases family_descends (prefixWord ++ tailWord_474361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474468 : List Nat := [2, 3, 1, 1, 3, 2, 1, 4, 4]
def baseStart_474468 : Nat := 118140960795 + 474468 * 2 ^ 59
def prefixEnd_474468 : Nat := 4983230072969 + 3 ^ 40 * 474468 * 2
def baseEnd_474468 : Nat := 108280061856691055763541

theorem tailTrace_474468 : CollatzResearch.WordTrace tailWord_474468 prefixEnd_474468 108280061856691055763541 := by
  unfold tailWord_474468
  simp only [CollatzResearch.WordTrace]
  refine ⟨8652634822545471764084029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11536846430060629018778705 8652634822545471764084029)
  ·
    refine ⟨3244738058454551911531511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8652634822545471764084029 3244738058454551911531511)
    ·
      refine ⟨4867107087681827867297267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3244738058454551911531511 4867107087681827867297267)
      ·
        refine ⟨7300660631522741800945901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4867107087681827867297267 7300660631522741800945901)
        ·
          refine ⟨2737747736821028175354713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7300660631522741800945901 2737747736821028175354713)
          ·
            refine ⟨2053310802615771131516035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2737747736821028175354713 2053310802615771131516035)
            ·
              refine ⟨3079966203923656697274053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2053310802615771131516035 3079966203923656697274053)
              ·
                refine ⟨577493663235685630738885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3079966203923656697274053 577493663235685630738885)
                ·
                  refine ⟨108280061856691055763541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 577493663235685630738885 108280061856691055763541)
                  ·
                    rfl

theorem cell21_474468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_474468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_474468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_474468 prefixEnd_474468 := by exact prefixLift 474468
  have htrace : WordTrace (prefixWord ++ tailWord_474468) baseStart_474468 baseEnd_474468 := by
    simpa [prefixWord, tailWord_474468, baseEnd_474468] using wordTrace_append hprefix tailTrace_474468
  have hstable : (prefixWord ++ tailWord_474468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474468).length < 2 ^ (prefixWord ++ tailWord_474468).sum := by decide
  have hdescent : baseEnd_474468 < baseStart_474468 := by decide
  rcases family_descends (prefixWord ++ tailWord_474468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474471 : List Nat := [1, 1, 5, 1, 4, 1, 1, 4, 3]
def baseStart_474471 : Nat := 118140960795 + 474471 * 2 ^ 59
def prefixEnd_474471 : Nat := 4983230072969 + 3 ^ 40 * 474471 * 2
def baseEnd_474471 : Nat := 108280746497563717213535

theorem tailTrace_474471 : CollatzResearch.WordTrace tailWord_474471 prefixEnd_474471 108280746497563717213535 := by
  unfold tailWord_474471
  simp only [CollatzResearch.WordTrace]
  refine ⟨17305379064080075040527267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11536919376053383360351511 17305379064080075040527267)
  ·
    refine ⟨25958068596120112560790901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17305379064080075040527267 25958068596120112560790901)
    ·
      refine ⟨2433568930886260552574147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25958068596120112560790901 2433568930886260552574147)
      ·
        refine ⟨3650353396329390828861221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2433568930886260552574147 3650353396329390828861221)
        ·
          refine ⟨684441261811760780411479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3650353396329390828861221 684441261811760780411479)
          ·
            refine ⟨1026661892717641170617219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684441261811760780411479 1026661892717641170617219)
            ·
              refine ⟨1539992839076461755925829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1026661892717641170617219 1539992839076461755925829)
              ·
                refine ⟨288748657326836579236093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1539992839076461755925829 288748657326836579236093)
                ·
                  refine ⟨108280746497563717213535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 288748657326836579236093 108280746497563717213535)
                  ·
                    rfl

theorem cell21_474471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 4, 3].length) (baseStart_474471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_474471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_474471 prefixEnd_474471 := by exact prefixLift 474471
  have htrace : WordTrace (prefixWord ++ tailWord_474471) baseStart_474471 baseEnd_474471 := by
    simpa [prefixWord, tailWord_474471, baseEnd_474471] using wordTrace_append hprefix tailTrace_474471
  have hstable : (prefixWord ++ tailWord_474471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474471).length < 2 ^ (prefixWord ++ tailWord_474471).sum := by decide
  have hdescent : baseEnd_474471 < baseStart_474471 := by decide
  rcases family_descends (prefixWord ++ tailWord_474471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474499 : List Nat := [1, 1, 1, 3, 5, 2, 3, 5]
def baseStart_474499 : Nat := 118140960795 + 474499 * 2 ^ 59
def prefixEnd_474499 : Nat := 4983230072969 + 3 ^ 40 * 474499 * 2
def baseEnd_474499 : Nat := 36095712159680630248937

theorem tailTrace_474499 : CollatzResearch.WordTrace tailWord_474499 prefixEnd_474499 36095712159680630248937 := by
  unfold tailWord_474499
  simp only [CollatzResearch.WordTrace]
  refine ⟨17306400307978635822546551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11537600205319090548364367 17306400307978635822546551)
  ·
    refine ⟨25959600461967953733819827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17306400307978635822546551 25959600461967953733819827)
    ·
      refine ⟨38939400692951930600729741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25959600461967953733819827 38939400692951930600729741)
      ·
        refine ⟨14602275259856973975273653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38939400692951930600729741 14602275259856973975273653)
        ·
          refine ⟨1368963305611591310181905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14602275259856973975273653 1368963305611591310181905)
          ·
            refine ⟨1026722479208693482636429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1368963305611591310181905 1026722479208693482636429)
            ·
              refine ⟨385020929703260055988661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1026722479208693482636429 385020929703260055988661)
              ·
                refine ⟨36095712159680630248937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 385020929703260055988661 36095712159680630248937)
                ·
                  rfl

theorem cell21_474499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 5].length) (baseStart_474499 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_474499 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_474499 prefixEnd_474499 := by exact prefixLift 474499
  have htrace : WordTrace (prefixWord ++ tailWord_474499) baseStart_474499 baseEnd_474499 := by
    simpa [prefixWord, tailWord_474499, baseEnd_474499] using wordTrace_append hprefix tailTrace_474499
  have hstable : (prefixWord ++ tailWord_474499).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474499).length < 2 ^ (prefixWord ++ tailWord_474499).sum := by decide
  have hdescent : baseEnd_474499 < baseStart_474499 := by decide
  rcases family_descends (prefixWord ++ tailWord_474499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474530 : List Nat := [3, 3, 1, 2, 1, 3, 2, 1, 5]
def baseStart_474530 : Nat := 118140960795 + 474530 * 2 ^ 59
def prefixEnd_474530 : Nat := 4983230072969 + 3 ^ 40 * 474530 * 2
def baseEnd_474530 : Nat := 108294211101392725730081

theorem tailTrace_474530 : CollatzResearch.WordTrace tailWord_474530 prefixEnd_474530 108294211101392725730081 := by
  unfold tailWord_474530
  simp only [CollatzResearch.WordTrace]
  refine ⟨4326882742716582029231261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11538353980577552077950029 4326882742716582029231261)
  ·
    refine ⟨1622581028518718260961723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4326882742716582029231261 1622581028518718260961723)
    ·
      refine ⟨2433871542778077391442585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1622581028518718260961723 2433871542778077391442585)
      ·
        refine ⟨1825403657083558043581939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2433871542778077391442585 1825403657083558043581939)
        ·
          refine ⟨2738105485625337065372909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1825403657083558043581939 2738105485625337065372909)
          ·
            refine ⟨1026789557109501399514841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2738105485625337065372909 1026789557109501399514841)
            ·
              refine ⟨770092167832126049636131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1026789557109501399514841 770092167832126049636131)
              ·
                refine ⟨1155138251748189074454197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 770092167832126049636131 1155138251748189074454197)
                ·
                  refine ⟨108294211101392725730081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1155138251748189074454197 108294211101392725730081)
                  ·
                    rfl

theorem cell21_474530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_474530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_474530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_474530 prefixEnd_474530 := by exact prefixLift 474530
  have htrace : WordTrace (prefixWord ++ tailWord_474530) baseStart_474530 baseEnd_474530 := by
    simpa [prefixWord, tailWord_474530, baseEnd_474530] using wordTrace_append hprefix tailTrace_474530
  have hstable : (prefixWord ++ tailWord_474530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474530).length < 2 ^ (prefixWord ++ tailWord_474530).sum := by decide
  have hdescent : baseEnd_474530 < baseStart_474530 := by decide
  rcases family_descends (prefixWord ++ tailWord_474530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474564 : List Nat := [2, 3, 3, 2, 1, 3, 1, 3, 3]
def baseStart_474564 : Nat := 118140960795 + 474564 * 2 ^ 59
def prefixEnd_474564 : Nat := 4983230072969 + 3 ^ 40 * 474564 * 2
def baseEnd_474564 : Nat := 108301970364616222163345

theorem tailTrace_474564 : CollatzResearch.WordTrace tailWord_474564 prefixEnd_474564 108301970364616222163345 := by
  unfold tailWord_474564
  simp only [CollatzResearch.WordTrace]
  refine ⟨8654385526371575961831373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11539180701828767949108497 8654385526371575961831373)
  ·
    refine ⟨3245394572389340985686765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8654385526371575961831373 3245394572389340985686765)
    ·
      refine ⟨1217022964646002869632537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3245394572389340985686765 1217022964646002869632537)
      ·
        refine ⟨912767223484502152224403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1217022964646002869632537 912767223484502152224403)
        ·
          refine ⟨1369150835226753228336605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 912767223484502152224403 1369150835226753228336605)
          ·
            refine ⟨513431563210032460626227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1369150835226753228336605 513431563210032460626227)
            ·
              refine ⟨770147344815048690939341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513431563210032460626227 770147344815048690939341)
              ·
                refine ⟨288805254305643259102253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 770147344815048690939341 288805254305643259102253)
                ·
                  refine ⟨108301970364616222163345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 288805254305643259102253 108301970364616222163345)
                  ·
                    rfl

theorem cell21_474564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_474564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_474564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_474564 prefixEnd_474564 := by exact prefixLift 474564
  have htrace : WordTrace (prefixWord ++ tailWord_474564) baseStart_474564 baseEnd_474564 := by
    simpa [prefixWord, tailWord_474564, baseEnd_474564] using wordTrace_append hprefix tailTrace_474564
  have hstable : (prefixWord ++ tailWord_474564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474564).length < 2 ^ (prefixWord ++ tailWord_474564).sum := by decide
  have hdescent : baseEnd_474564 < baseStart_474564 := by decide
  rcases family_descends (prefixWord ++ tailWord_474564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474682 : List Nat := [3, 1, 1, 1, 3, 2, 4, 3, 3]
def baseStart_474682 : Nat := 118140960795 + 474682 * 2 ^ 59
def prefixEnd_474682 : Nat := 4983230072969 + 3 ^ 40 * 474682 * 2
def baseEnd_474682 : Nat := 108328899572274239196437

theorem tailTrace_474682 : CollatzResearch.WordTrace tailWord_474682 prefixEnd_474682 108328899572274239196437 := by
  unfold tailWord_474682
  simp only [CollatzResearch.WordTrace]
  refine ⟨4328268716578914519114575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11542049910877105384305533 4328268716578914519114575)
  ·
    refine ⟨6492403074868371778671863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4328268716578914519114575 6492403074868371778671863)
    ·
      refine ⟨9738604612302557668007795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6492403074868371778671863 9738604612302557668007795)
      ·
        refine ⟨14607906918453836502011693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9738604612302557668007795 14607906918453836502011693)
        ·
          refine ⟨5477965094420188688254385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14607906918453836502011693 5477965094420188688254385)
          ·
            refine ⟨4108473820815141516190789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5477965094420188688254385 4108473820815141516190789)
            ·
              refine ⟨770338841402839034285773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4108473820815141516190789 770338841402839034285773)
              ·
                refine ⟨288877065526064637857165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 770338841402839034285773 288877065526064637857165)
                ·
                  refine ⟨108328899572274239196437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 288877065526064637857165 108328899572274239196437)
                  ·
                    rfl

theorem cell21_474682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 3, 3].length) (baseStart_474682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_474682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_474682 prefixEnd_474682 := by exact prefixLift 474682
  have htrace : WordTrace (prefixWord ++ tailWord_474682) baseStart_474682 baseEnd_474682 := by
    simpa [prefixWord, tailWord_474682, baseEnd_474682] using wordTrace_append hprefix tailTrace_474682
  have hstable : (prefixWord ++ tailWord_474682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474682).length < 2 ^ (prefixWord ++ tailWord_474682).sum := by decide
  have hdescent : baseEnd_474682 < baseStart_474682 := by decide
  rcases family_descends (prefixWord ++ tailWord_474682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474693 : List Nat := [1, 3, 1, 1, 1, 4, 10]
def baseStart_474693 : Nat := 118140960795 + 474693 * 2 ^ 59
def prefixEnd_474693 : Nat := 4983230072969 + 3 ^ 40 * 474693 * 2
def baseEnd_474693 : Nat := 12036823324682296057009

theorem tailTrace_474693 : CollatzResearch.WordTrace tailWord_474693 prefixEnd_474693 12036823324682296057009 := by
  unfold tailWord_474693
  simp only [CollatzResearch.WordTrace]
  refine ⟨17313476069275806955108733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11542317379517204636739155 17313476069275806955108733)
  ·
    refine ⟨6492553525978427608165775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17313476069275806955108733 6492553525978427608165775)
    ·
      refine ⟨9738830288967641412248663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6492553525978427608165775 9738830288967641412248663)
      ·
        refine ⟨14608245433451462118372995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9738830288967641412248663 14608245433451462118372995)
        ·
          refine ⟨21912368150177193177559493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14608245433451462118372995 21912368150177193177559493)
          ·
            refine ⟨4108569028158223720792405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21912368150177193177559493 4108569028158223720792405)
            ·
              refine ⟨12036823324682296057009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4108569028158223720792405 12036823324682296057009)
              ·
                rfl

theorem cell21_474693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 10].length) (baseStart_474693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_474693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_474693 prefixEnd_474693 := by exact prefixLift 474693
  have htrace : WordTrace (prefixWord ++ tailWord_474693) baseStart_474693 baseEnd_474693 := by
    simpa [prefixWord, tailWord_474693, baseEnd_474693] using wordTrace_append hprefix tailTrace_474693
  have hstable : (prefixWord ++ tailWord_474693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474693).length < 2 ^ (prefixWord ++ tailWord_474693).sum := by decide
  have hdescent : baseEnd_474693 < baseStart_474693 := by decide
  rcases family_descends (prefixWord ++ tailWord_474693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474755 : List Nat := [1, 1, 1, 3, 3, 1, 1, 6, 4]
def baseStart_474755 : Nat := 118140960795 + 474755 * 2 ^ 59
def prefixEnd_474755 : Nat := 4983230072969 + 3 ^ 40 * 474755 * 2
def baseEnd_474755 : Nat := 108345559166842334479621

theorem tailTrace_474755 : CollatzResearch.WordTrace tailWord_474755 prefixEnd_474755 108345559166842334479621 := by
  unfold tailWord_474755
  simp only [CollatzResearch.WordTrace]
  refine ⟨17315737395051191543865719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11543824930034127695910479 17315737395051191543865719)
  ·
    refine ⟨25973606092576787315798579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17315737395051191543865719 25973606092576787315798579)
    ·
      refine ⟨38960409138865180973697869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25973606092576787315798579 38960409138865180973697869)
      ·
        refine ⟨14610153427074442865136701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38960409138865180973697869 14610153427074442865136701)
        ·
          refine ⟨5478807535152916074426263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14610153427074442865136701 5478807535152916074426263)
          ·
            refine ⟨8218211302729374111639395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5478807535152916074426263 8218211302729374111639395)
            ·
              refine ⟨12327316954094061167459093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8218211302729374111639395 12327316954094061167459093)
              ·
                refine ⟨577842982223159117224645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12327316954094061167459093 577842982223159117224645)
                ·
                  refine ⟨108345559166842334479621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 577842982223159117224645 108345559166842334479621)
                  ·
                    rfl

theorem cell21_474755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 4].length) (baseStart_474755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_474755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_474755 prefixEnd_474755 := by exact prefixLift 474755
  have htrace : WordTrace (prefixWord ++ tailWord_474755) baseStart_474755 baseEnd_474755 := by
    simpa [prefixWord, tailWord_474755, baseEnd_474755] using wordTrace_append hprefix tailTrace_474755
  have hstable : (prefixWord ++ tailWord_474755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474755).length < 2 ^ (prefixWord ++ tailWord_474755).sum := by decide
  have hdescent : baseEnd_474755 < baseStart_474755 := by decide
  rcases family_descends (prefixWord ++ tailWord_474755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474806 : List Nat := [5, 1, 3, 1, 1, 2, 2, 2, 4]
def baseStart_474806 : Nat := 118140960795 + 474806 * 2 ^ 59
def prefixEnd_474806 : Nat := 4983230072969 + 3 ^ 40 * 474806 * 2
def baseEnd_474806 : Nat := 108357198061677579129517

theorem tailTrace_474806 : CollatzResearch.WordTrace tailWord_474806 prefixEnd_474806 108357198061677579129517 := by
  unfold tailWord_474806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1082349844866651703373267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11545065011910951502648181 1082349844866651703373267)
  ·
    refine ⟨1623524767299977555059901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1082349844866651703373267 1623524767299977555059901)
    ·
      refine ⟨608821787737491583147463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1623524767299977555059901 608821787737491583147463)
      ·
        refine ⟨913232681606237374721195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608821787737491583147463 913232681606237374721195)
        ·
          refine ⟨1369849022409356062081793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 913232681606237374721195 1369849022409356062081793)
          ·
            refine ⟨1027386766807017046561345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1369849022409356062081793 1027386766807017046561345)
            ·
              refine ⟨770540075105262784921009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1027386766807017046561345 770540075105262784921009)
              ·
                refine ⟨577905056328947088690757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 770540075105262784921009 577905056328947088690757)
                ·
                  refine ⟨108357198061677579129517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 577905056328947088690757 108357198061677579129517)
                  ·
                    rfl

theorem cell21_474806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_474806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_474806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_474806 prefixEnd_474806 := by exact prefixLift 474806
  have htrace : WordTrace (prefixWord ++ tailWord_474806) baseStart_474806 baseEnd_474806 := by
    simpa [prefixWord, tailWord_474806, baseEnd_474806] using wordTrace_append hprefix tailTrace_474806
  have hstable : (prefixWord ++ tailWord_474806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474806).length < 2 ^ (prefixWord ++ tailWord_474806).sum := by decide
  have hdescent : baseEnd_474806 < baseStart_474806 := by decide
  rcases family_descends (prefixWord ++ tailWord_474806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474851 : List Nat := [1, 1, 1, 7, 2, 1, 2, 3, 3]
def baseStart_474851 : Nat := 118140960795 + 474851 * 2 ^ 59
def prefixEnd_474851 : Nat := 4983230072969 + 3 ^ 40 * 474851 * 2
def baseEnd_474851 : Nat := 108367467674767500879425

theorem tailTrace_474851 : CollatzResearch.WordTrace tailWord_474851 prefixEnd_474851 108367467674767500879425 := by
  unfold tailWord_474851
  simp only [CollatzResearch.WordTrace]
  refine ⟨17319238802703399939360407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11546159201802266626240271 17319238802703399939360407)
  ·
    refine ⟨25978858204055099909040611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17319238802703399939360407 25978858204055099909040611)
    ·
      refine ⟨38968287306082649863560917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25978858204055099909040611 38968287306082649863560917)
      ·
        refine ⟨913319233736312106177209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 38968287306082649863560917 913319233736312106177209)
        ·
          refine ⟨684989425302234079632907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 913319233736312106177209 684989425302234079632907)
          ·
            refine ⟨1027484137953351119449361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684989425302234079632907 1027484137953351119449361)
            ·
              refine ⟨770613103465013339587021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1027484137953351119449361 770613103465013339587021)
              ·
                refine ⟨288979913799380002345133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 770613103465013339587021 288979913799380002345133)
                ·
                  refine ⟨108367467674767500879425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 288979913799380002345133 108367467674767500879425)
                  ·
                    rfl

theorem cell21_474851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 3, 3].length) (baseStart_474851 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_474851 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_474851 prefixEnd_474851 := by exact prefixLift 474851
  have htrace : WordTrace (prefixWord ++ tailWord_474851) baseStart_474851 baseEnd_474851 := by
    simpa [prefixWord, tailWord_474851, baseEnd_474851] using wordTrace_append hprefix tailTrace_474851
  have hstable : (prefixWord ++ tailWord_474851).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474851).length < 2 ^ (prefixWord ++ tailWord_474851).sum := by decide
  have hdescent : baseEnd_474851 < baseStart_474851 := by decide
  rcases family_descends (prefixWord ++ tailWord_474851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474868 : List Nat := [2, 6, 1, 1, 1, 1, 2, 4, 3]
def baseStart_474868 : Nat := 118140960795 + 474868 * 2 ^ 59
def prefixEnd_474868 : Nat := 4983230072969 + 3 ^ 40 * 474868 * 2
def baseEnd_474868 : Nat := 108371347306379249096057

theorem tailTrace_474868 : CollatzResearch.WordTrace tailWord_474868 prefixEnd_474868 108371347306379249096057 := by
  unfold tailWord_474868
  simp only [CollatzResearch.WordTrace]
  refine ⟨8659929421820905921364629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11546572562427874561819505 8659929421820905921364629)
  ·
    refine ⟨405934191647854965063967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8659929421820905921364629 405934191647854965063967)
    ·
      refine ⟨608901287471782447595951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405934191647854965063967 608901287471782447595951)
      ·
        refine ⟨913351931207673671393927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608901287471782447595951 913351931207673671393927)
        ·
          refine ⟨1370027896811510507090891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 913351931207673671393927 1370027896811510507090891)
          ·
            refine ⟨2055041845217265760636337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1370027896811510507090891 2055041845217265760636337)
            ·
              refine ⟨1541281383912949320477253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2055041845217265760636337 1541281383912949320477253)
              ·
                refine ⟨288990259483677997589485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1541281383912949320477253 288990259483677997589485)
                ·
                  refine ⟨108371347306379249096057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 288990259483677997589485 108371347306379249096057)
                  ·
                    rfl

theorem cell21_474868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_474868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_474868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_474868 prefixEnd_474868 := by exact prefixLift 474868
  have htrace : WordTrace (prefixWord ++ tailWord_474868) baseStart_474868 baseEnd_474868 := by
    simpa [prefixWord, tailWord_474868, baseEnd_474868] using wordTrace_append hprefix tailTrace_474868
  have hstable : (prefixWord ++ tailWord_474868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474868).length < 2 ^ (prefixWord ++ tailWord_474868).sum := by decide
  have hdescent : baseEnd_474868 < baseStart_474868 := by decide
  rcases family_descends (prefixWord ++ tailWord_474868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474938 : List Nat := [3, 1, 1, 1, 5, 2, 2, 6]
def baseStart_474938 : Nat := 118140960795 + 474938 * 2 ^ 59
def prefixEnd_474938 : Nat := 4983230072969 + 3 ^ 40 * 474938 * 2
def baseEnd_474938 : Nat := 36129107420024894309749

theorem tailTrace_474938 : CollatzResearch.WordTrace tailWord_474938 prefixEnd_474938 36129107420024894309749 := by
  unfold tailWord_474938
  simp only [CollatzResearch.WordTrace]
  refine ⟨4330602988347053449444367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11548274635592142531851645 4330602988347053449444367)
  ·
    refine ⟨6495904482520580174166551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4330602988347053449444367 6495904482520580174166551)
    ·
      refine ⟨9743856723780870261249827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6495904482520580174166551 9743856723780870261249827)
      ·
        refine ⟨14615785085671305391874741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9743856723780870261249827 14615785085671305391874741)
        ·
          refine ⟨1370229851781684880488257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14615785085671305391874741 1370229851781684880488257)
          ·
            refine ⟨1027672388836263660366193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1370229851781684880488257 1027672388836263660366193)
            ·
              refine ⟨770754291627197745274645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1027672388836263660366193 770754291627197745274645)
              ·
                refine ⟨36129107420024894309749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 770754291627197745274645 36129107420024894309749)
                ·
                  rfl

theorem cell21_474938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 6].length) (baseStart_474938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_474938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_474938 prefixEnd_474938 := by exact prefixLift 474938
  have htrace : WordTrace (prefixWord ++ tailWord_474938) baseStart_474938 baseEnd_474938 := by
    simpa [prefixWord, tailWord_474938, baseEnd_474938] using wordTrace_append hprefix tailTrace_474938
  have hstable : (prefixWord ++ tailWord_474938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474938).length < 2 ^ (prefixWord ++ tailWord_474938).sum := by decide
  have hdescent : baseEnd_474938 < baseStart_474938 := by decide
  rcases family_descends (prefixWord ++ tailWord_474938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474941 : List Nat := [1, 4, 1, 4, 1, 1, 4, 1, 4]
def baseStart_474941 : Nat := 118140960795 + 474941 * 2 ^ 59
def prefixEnd_474941 : Nat := 4983230072969 + 3 ^ 40 * 474941 * 2
def baseEnd_474941 : Nat := 108388006900947344379241

theorem tailTrace_474941 : CollatzResearch.WordTrace tailWord_474941 prefixEnd_474941 108388006900947344379241 := by
  unfold tailWord_474941
  simp only [CollatzResearch.WordTrace]
  refine ⟨17322521372377345310136677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11548347581584896873424451 17322521372377345310136677)
  ·
    refine ⟨3247972757320752245650627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17322521372377345310136677 3247972757320752245650627)
    ·
      refine ⟨4871959135981128368475941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3247972757320752245650627 4871959135981128368475941)
      ·
        refine ⟨913492337996461569089239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4871959135981128368475941 913492337996461569089239)
        ·
          refine ⟨1370238506994692353633859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 913492337996461569089239 1370238506994692353633859)
          ·
            refine ⟨2055357760492038530450789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1370238506994692353633859 2055357760492038530450789)
            ·
              refine ⟨385379580092257224459523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2055357760492038530450789 385379580092257224459523)
              ·
                refine ⟨578069370138385836689285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385379580092257224459523 578069370138385836689285)
                ·
                  refine ⟨108388006900947344379241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 578069370138385836689285 108388006900947344379241)
                  ·
                    rfl

theorem cell21_474941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_474941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_474941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_474941 prefixEnd_474941 := by exact prefixLift 474941
  have htrace : WordTrace (prefixWord ++ tailWord_474941) baseStart_474941 baseEnd_474941 := by
    simpa [prefixWord, tailWord_474941, baseEnd_474941] using wordTrace_append hprefix tailTrace_474941
  have hstable : (prefixWord ++ tailWord_474941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474941).length < 2 ^ (prefixWord ++ tailWord_474941).sum := by decide
  have hdescent : baseEnd_474941 < baseStart_474941 := by decide
  rcases family_descends (prefixWord ++ tailWord_474941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474969 : List Nat := [1, 2, 1, 2, 2, 3, 2, 5, 3]
def baseStart_474969 : Nat := 118140960795 + 474969 * 2 ^ 59
def prefixEnd_474969 : Nat := 4983230072969 + 3 ^ 40 * 474969 * 2
def baseEnd_474969 : Nat := 108394396882425517912517

theorem tailTrace_474969 : CollatzResearch.WordTrace tailWord_474969 prefixEnd_474969 108394396882425517912517 := by
  unfold tailWord_474969
  simp only [CollatzResearch.WordTrace]
  refine ⟨17323542616275906092155961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11549028410850604061437307 17323542616275906092155961)
  ·
    refine ⟨12992656962206929569116971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17323542616275906092155961 12992656962206929569116971)
    ·
      refine ⟨19488985443310394353675457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12992656962206929569116971 19488985443310394353675457)
      ·
        refine ⟨14616739082482795765256593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19488985443310394353675457 14616739082482795765256593)
        ·
          refine ⟨10962554311862096823942445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14616739082482795765256593 10962554311862096823942445)
          ·
            refine ⟨4110957866948286308978417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10962554311862096823942445 4110957866948286308978417)
            ·
              refine ⟨3083218400211214731733813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4110957866948286308978417 3083218400211214731733813)
              ·
                refine ⟨289051725019801381100045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3083218400211214731733813 289051725019801381100045)
                ·
                  refine ⟨108394396882425517912517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 289051725019801381100045 108394396882425517912517)
                  ·
                    rfl

theorem cell21_474969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 5, 3].length) (baseStart_474969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_474969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_474969 prefixEnd_474969 := by exact prefixLift 474969
  have htrace : WordTrace (prefixWord ++ tailWord_474969) baseStart_474969 baseEnd_474969 := by
    simpa [prefixWord, tailWord_474969, baseEnd_474969] using wordTrace_append hprefix tailTrace_474969
  have hstable : (prefixWord ++ tailWord_474969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474969).length < 2 ^ (prefixWord ++ tailWord_474969).sum := by decide
  have hdescent : baseEnd_474969 < baseStart_474969 := by decide
  rcases family_descends (prefixWord ++ tailWord_474969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475194 : List Nat := [3, 1, 1, 1, 3, 1, 1, 4, 6]
def baseStart_475194 : Nat := 118140960795 + 475194 * 2 ^ 59
def prefixEnd_475194 : Nat := 4983230072969 + 3 ^ 40 * 475194 * 2
def baseEnd_475194 : Nat := 108445744947875126662057

theorem tailTrace_475194 : CollatzResearch.WordTrace tailWord_475194 prefixEnd_475194 108445744947875126662057 := by
  unfold tailWord_475194
  simp only [CollatzResearch.WordTrace]
  refine ⟨4332937260115192379774159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11554499360307179679397757 4332937260115192379774159)
  ·
    refine ⟨6499405890172788569661239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4332937260115192379774159 6499405890172788569661239)
    ·
      refine ⟨9749108835259182854491859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6499405890172788569661239 9749108835259182854491859)
      ·
        refine ⟨14623663252888774281737789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9749108835259182854491859 14623663252888774281737789)
        ·
          refine ⟨5483873719833290355651671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14623663252888774281737789 5483873719833290355651671)
          ·
            refine ⟨8225810579749935533477507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5483873719833290355651671 8225810579749935533477507)
            ·
              refine ⟨12338715869624903300216261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8225810579749935533477507 12338715869624903300216261)
              ·
                refine ⟨2313509225554669368790549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12338715869624903300216261 2313509225554669368790549)
                ·
                  refine ⟨108445744947875126662057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2313509225554669368790549 108445744947875126662057)
                  ·
                    rfl

theorem cell21_475194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_475194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_475194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_475194 prefixEnd_475194 := by exact prefixLift 475194
  have htrace : WordTrace (prefixWord ++ tailWord_475194) baseStart_475194 baseEnd_475194 := by
    simpa [prefixWord, tailWord_475194, baseEnd_475194] using wordTrace_append hprefix tailTrace_475194
  have hstable : (prefixWord ++ tailWord_475194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475194).length < 2 ^ (prefixWord ++ tailWord_475194).sum := by decide
  have hdescent : baseEnd_475194 < baseStart_475194 := by decide
  rcases family_descends (prefixWord ++ tailWord_475194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475242 : List Nat := [3, 1, 3, 2, 3, 1, 1, 7]
def baseStart_475242 : Nat := 118140960795 + 475242 * 2 ^ 59
def prefixEnd_475242 : Nat := 4983230072969 + 3 ^ 40 * 475242 * 2
def baseEnd_475242 : Nat := 36152233067279236620653

theorem tailTrace_475242 : CollatzResearch.WordTrace tailWord_475242 prefixEnd_475242 36152233067279236620653 := by
  unfold tailWord_475242
  simp only [CollatzResearch.WordTrace]
  refine ⟨4333374936071718429210995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11555666496191249144562653 4333374936071718429210995)
  ·
    refine ⟨6500062404107577643816493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4333374936071718429210995 6500062404107577643816493)
    ·
      refine ⟨2437523401540341616431185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6500062404107577643816493 2437523401540341616431185)
      ·
        refine ⟨1828142551155256212323389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2437523401540341616431185 1828142551155256212323389)
        ·
          refine ⟨685553456683221079621271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1828142551155256212323389 685553456683221079621271)
          ·
            refine ⟨1028330185024831619431907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685553456683221079621271 1028330185024831619431907)
            ·
              refine ⟨1542495277537247429147861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1028330185024831619431907 1542495277537247429147861)
              ·
                refine ⟨36152233067279236620653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1542495277537247429147861 36152233067279236620653)
                ·
                  rfl

theorem cell21_475242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 7].length) (baseStart_475242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_475242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_475242 prefixEnd_475242 := by exact prefixLift 475242
  have htrace : WordTrace (prefixWord ++ tailWord_475242) baseStart_475242 baseEnd_475242 := by
    simpa [prefixWord, tailWord_475242, baseEnd_475242] using wordTrace_append hprefix tailTrace_475242
  have hstable : (prefixWord ++ tailWord_475242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475242).length < 2 ^ (prefixWord ++ tailWord_475242).sum := by decide
  have hdescent : baseEnd_475242 < baseStart_475242 := by decide
  rcases family_descends (prefixWord ++ tailWord_475242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475324 : List Nat := [2, 2, 2, 3, 4, 1, 2, 2, 3]
def baseStart_475324 : Nat := 118140960795 + 475324 * 2 ^ 59
def prefixEnd_475324 : Nat := 4983230072969 + 3 ^ 40 * 475324 * 2
def baseEnd_475324 : Nat := 108475412719023789495125

theorem tailTrace_475324 : CollatzResearch.WordTrace tailWord_475324 prefixEnd_475324 108475412719023789495125 := by
  unfold tailWord_475324
  simp only [CollatzResearch.WordTrace]
  refine ⟨8668245264994900860664513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11557660353326534480886017 8668245264994900860664513)
  ·
    refine ⟨6501183948746175645498385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8668245264994900860664513 6501183948746175645498385)
    ·
      refine ⟨4875887961559631734123789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6501183948746175645498385 4875887961559631734123789)
      ·
        refine ⟨1828457985584861900296421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4875887961559631734123789 1828457985584861900296421)
        ·
          refine ⟨342835872297161606305579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1828457985584861900296421 342835872297161606305579)
          ·
            refine ⟨514253808445742409458369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342835872297161606305579 514253808445742409458369)
            ·
              refine ⟨385690356334306807093777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 514253808445742409458369 385690356334306807093777)
              ·
                refine ⟨289267767250730105320333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385690356334306807093777 289267767250730105320333)
                ·
                  refine ⟨108475412719023789495125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 289267767250730105320333 108475412719023789495125)
                  ·
                    rfl

theorem cell21_475324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 2, 3].length) (baseStart_475324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_475324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_475324 prefixEnd_475324 := by exact prefixLift 475324
  have htrace : WordTrace (prefixWord ++ tailWord_475324) baseStart_475324 baseEnd_475324 := by
    simpa [prefixWord, tailWord_475324, baseEnd_475324] using wordTrace_append hprefix tailTrace_475324
  have hstable : (prefixWord ++ tailWord_475324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475324).length < 2 ^ (prefixWord ++ tailWord_475324).sum := by decide
  have hdescent : baseEnd_475324 < baseStart_475324 := by decide
  rcases family_descends (prefixWord ++ tailWord_475324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475349 : List Nat := [1, 3, 2, 4, 2, 1, 1, 2, 5]
def baseStart_475349 : Nat := 118140960795 + 475349 * 2 ^ 59
def prefixEnd_475349 : Nat := 4983230072969 + 3 ^ 40 * 475349 * 2
def baseEnd_475349 : Nat := 108481118059629301578407

theorem tailTrace_475349 : CollatzResearch.WordTrace tailWord_475349 prefixEnd_475349 108481118059629301578407 := by
  unfold tailWord_475349
  simp only [CollatzResearch.WordTrace]
  refine ⟨17337402354899230990989101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11558268236599487327326067 17337402354899230990989101)
  ·
    refine ⟨6501525883087211621620913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17337402354899230990989101 6501525883087211621620913)
    ·
      refine ⟨4876144412315408716215685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6501525883087211621620913 4876144412315408716215685)
      ·
        refine ⟨914277077309139134290441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4876144412315408716215685 914277077309139134290441)
        ·
          refine ⟨685707807981854350717831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 914277077309139134290441 685707807981854350717831)
          ·
            refine ⟨1028561711972781526076747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685707807981854350717831 1028561711972781526076747)
            ·
              refine ⟨1542842567959172289115121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1028561711972781526076747 1542842567959172289115121)
              ·
                refine ⟨1157131925969379216836341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1542842567959172289115121 1157131925969379216836341)
                ·
                  refine ⟨108481118059629301578407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1157131925969379216836341 108481118059629301578407)
                  ·
                    rfl

theorem cell21_475349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_475349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_475349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_475349 prefixEnd_475349 := by exact prefixLift 475349
  have htrace : WordTrace (prefixWord ++ tailWord_475349) baseStart_475349 baseEnd_475349 := by
    simpa [prefixWord, tailWord_475349, baseEnd_475349] using wordTrace_append hprefix tailTrace_475349
  have hstable : (prefixWord ++ tailWord_475349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475349).length < 2 ^ (prefixWord ++ tailWord_475349).sum := by decide
  have hdescent : baseEnd_475349 < baseStart_475349 := by decide
  rcases family_descends (prefixWord ++ tailWord_475349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475425 : List Nat := [1, 2, 3, 2, 1, 1, 5, 3, 3]
def baseStart_475425 : Nat := 118140960795 + 475425 * 2 ^ 59
def prefixEnd_475425 : Nat := 4983230072969 + 3 ^ 40 * 475425 * 2
def baseEnd_475425 : Nat := 108498462295070058311585

theorem tailTrace_475425 : CollatzResearch.WordTrace tailWord_475425 prefixEnd_475425 108498462295070058311585 := by
  unfold tailWord_475425
  simp only [CollatzResearch.WordTrace]
  refine ⟨17340174302623895970755729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11560116201749263980503819 17340174302623895970755729)
  ·
    refine ⟨13005130726967921978066797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17340174302623895970755729 13005130726967921978066797)
    ·
      refine ⟨4876924022612970741775049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13005130726967921978066797 4876924022612970741775049)
      ·
        refine ⟨3657693016959728056331287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4876924022612970741775049 3657693016959728056331287)
        ·
          refine ⟨5486539525439592084496931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3657693016959728056331287 5486539525439592084496931)
          ·
            refine ⟨8229809288159388126745397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5486539525439592084496931 8229809288159388126745397)
            ·
              refine ⟨771544620764942636882381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8229809288159388126745397 771544620764942636882381)
              ·
                refine ⟨289329232786853488830893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 771544620764942636882381 289329232786853488830893)
                ·
                  refine ⟨108498462295070058311585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 289329232786853488830893 108498462295070058311585)
                  ·
                    rfl

theorem cell21_475425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 3, 3].length) (baseStart_475425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_475425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_475425 prefixEnd_475425 := by exact prefixLift 475425
  have htrace : WordTrace (prefixWord ++ tailWord_475425) baseStart_475425 baseEnd_475425 := by
    simpa [prefixWord, tailWord_475425, baseEnd_475425] using wordTrace_append hprefix tailTrace_475425
  have hstable : (prefixWord ++ tailWord_475425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475425).length < 2 ^ (prefixWord ++ tailWord_475425).sum := by decide
  have hdescent : baseEnd_475425 < baseStart_475425 := by decide
  rcases family_descends (prefixWord ++ tailWord_475425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475436 : List Nat := [2, 2, 1, 1, 1, 3, 11]
def baseStart_475436 : Nat := 118140960795 + 475436 * 2 ^ 59
def prefixEnd_475436 : Nat := 4983230072969 + 3 ^ 40 * 475436 * 2
def baseEnd_475436 : Nat := 12055663627215164847581

theorem tailTrace_475436 : CollatzResearch.WordTrace tailWord_475436 prefixEnd_475436 12055663627215164847581 := by
  unfold tailWord_475436
  simp only [CollatzResearch.WordTrace]
  refine ⟨8670287752792022424703081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11560383670389363232937441 8670287752792022424703081)
  ·
    refine ⟨6502715814594016818527311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8670287752792022424703081 6502715814594016818527311)
    ·
      refine ⟨9754073721891025227790967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6502715814594016818527311 9754073721891025227790967)
      ·
        refine ⟨14631110582836537841686451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9754073721891025227790967 14631110582836537841686451)
        ·
          refine ⟨21946665874254806762529677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14631110582836537841686451 21946665874254806762529677)
          ·
            refine ⟨8229999702845552535948629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21946665874254806762529677 8229999702845552535948629)
            ·
              refine ⟨12055663627215164847581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 8229999702845552535948629 12055663627215164847581)
              ·
                rfl

theorem cell21_475436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 11].length) (baseStart_475436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_475436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_475436 prefixEnd_475436 := by exact prefixLift 475436
  have htrace : WordTrace (prefixWord ++ tailWord_475436) baseStart_475436 baseEnd_475436 := by
    simpa [prefixWord, tailWord_475436, baseEnd_475436] using wordTrace_append hprefix tailTrace_475436
  have hstable : (prefixWord ++ tailWord_475436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475436).length < 2 ^ (prefixWord ++ tailWord_475436).sum := by decide
  have hdescent : baseEnd_475436 < baseStart_475436 := by decide
  rcases family_descends (prefixWord ++ tailWord_475436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475442 : List Nat := [3, 2, 1, 1, 6, 1, 1, 1, 5]
def baseStart_475442 : Nat := 118140960795 + 475442 * 2 ^ 59
def prefixEnd_475442 : Nat := 4983230072969 + 3 ^ 40 * 475442 * 2
def baseEnd_475442 : Nat := 108502341926681806528217

theorem tailTrace_475442 : CollatzResearch.WordTrace tailWord_475442 prefixEnd_475442 108502341926681806528217 := by
  unfold tailWord_475442
  simp only [CollatzResearch.WordTrace]
  refine ⟨4335198585890576968531145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11560529562374871916083053 4335198585890576968531145)
  ·
    refine ⟨3251398939417932726398359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4335198585890576968531145 3251398939417932726398359)
    ·
      refine ⟨4877098409126899089597539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3251398939417932726398359 4877098409126899089597539)
      ·
        refine ⟨7315647613690348634396309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4877098409126899089597539 7315647613690348634396309)
        ·
          refine ⟨342920981891735092237327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7315647613690348634396309 342920981891735092237327)
          ·
            refine ⟨514381472837602638355991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342920981891735092237327 514381472837602638355991)
            ·
              refine ⟨771572209256403957533987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 514381472837602638355991 771572209256403957533987)
              ·
                refine ⟨1157358313884605936300981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 771572209256403957533987 1157358313884605936300981)
                ·
                  refine ⟨108502341926681806528217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1157358313884605936300981 108502341926681806528217)
                  ·
                    rfl

theorem cell21_475442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_475442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_475442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_475442 prefixEnd_475442 := by exact prefixLift 475442
  have htrace : WordTrace (prefixWord ++ tailWord_475442) baseStart_475442 baseEnd_475442 := by
    simpa [prefixWord, tailWord_475442, baseEnd_475442] using wordTrace_append hprefix tailTrace_475442
  have hstable : (prefixWord ++ tailWord_475442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475442).length < 2 ^ (prefixWord ++ tailWord_475442).sum := by decide
  have hdescent : baseEnd_475442 < baseStart_475442 := by decide
  rcases family_descends (prefixWord ++ tailWord_475442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475501 : List Nat := [1, 5, 1, 1, 1, 2, 3, 4, 3]
def baseStart_475501 : Nat := 118140960795 + 475501 * 2 ^ 59
def prefixEnd_475501 : Nat := 4983230072969 + 3 ^ 40 * 475501 * 2
def baseEnd_475501 : Nat := 108515806530510815044763

theorem tailTrace_475501 : CollatzResearch.WordTrace tailWord_475501 prefixEnd_475501 108515806530510815044763 := by
  unfold tailWord_475501
  simp only [CollatzResearch.WordTrace]
  refine ⟨17342946250348560950522357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11561964166899040633681571 17342946250348560950522357)
  ·
    refine ⟨1625901210970177589111471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17342946250348560950522357 1625901210970177589111471)
    ·
      refine ⟨2438851816455266383667207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1625901210970177589111471 2438851816455266383667207)
      ·
        refine ⟨3658277724682899575500811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2438851816455266383667207 3658277724682899575500811)
        ·
          refine ⟨5487416587024349363251217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3658277724682899575500811 5487416587024349363251217)
          ·
            refine ⟨4115562440268262022438413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5487416587024349363251217 4115562440268262022438413)
            ·
              refine ⟨1543335915100598258414405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4115562440268262022438413 1543335915100598258414405)
              ·
                refine ⟨289375484081362173452701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1543335915100598258414405 289375484081362173452701)
                ·
                  refine ⟨108515806530510815044763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 289375484081362173452701 108515806530510815044763)
                  ·
                    rfl

theorem cell21_475501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_475501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_475501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_475501 prefixEnd_475501 := by exact prefixLift 475501
  have htrace : WordTrace (prefixWord ++ tailWord_475501) baseStart_475501 baseEnd_475501 := by
    simpa [prefixWord, tailWord_475501, baseEnd_475501] using wordTrace_append hprefix tailTrace_475501
  have hstable : (prefixWord ++ tailWord_475501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475501).length < 2 ^ (prefixWord ++ tailWord_475501).sum := by decide
  have hdescent : baseEnd_475501 < baseStart_475501 := by decide
  rcases family_descends (prefixWord ++ tailWord_475501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475549 : List Nat := [1, 4, 2, 1, 5, 1, 1, 2, 4]
def baseStart_475549 : Nat := 118140960795 + 475549 * 2 ^ 59
def prefixEnd_475549 : Nat := 4983230072969 + 3 ^ 40 * 475549 * 2
def baseEnd_475549 : Nat := 108526760784473398244665

theorem tailTrace_475549 : CollatzResearch.WordTrace tailWord_475549 prefixEnd_475549 108526760784473398244665 := by
  unfold tailWord_475549
  simp only [CollatzResearch.WordTrace]
  refine ⟨17344696954174665148269701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11563131302783110098846467 17344696954174665148269701)
  ·
    refine ⟨3252130678907749715300569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17344696954174665148269701 3252130678907749715300569)
    ·
      refine ⟨2439098009180812286475427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3252130678907749715300569 2439098009180812286475427)
      ·
        refine ⟨3658647013771218429713141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2439098009180812286475427 3658647013771218429713141)
        ·
          refine ⟨342998157541051727785607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3658647013771218429713141 342998157541051727785607)
          ·
            refine ⟨514497236311577591678411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342998157541051727785607 514497236311577591678411)
            ·
              refine ⟨771745854467366387517617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 514497236311577591678411 771745854467366387517617)
              ·
                refine ⟨578809390850524790638213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 771745854467366387517617 578809390850524790638213)
                ·
                  refine ⟨108526760784473398244665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 578809390850524790638213 108526760784473398244665)
                  ·
                    rfl

theorem cell21_475549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_475549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_475549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_475549 prefixEnd_475549 := by exact prefixLift 475549
  have htrace : WordTrace (prefixWord ++ tailWord_475549) baseStart_475549 baseEnd_475549 := by
    simpa [prefixWord, tailWord_475549, baseEnd_475549] using wordTrace_append hprefix tailTrace_475549
  have hstable : (prefixWord ++ tailWord_475549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475549).length < 2 ^ (prefixWord ++ tailWord_475549).sum := by decide
  have hdescent : baseEnd_475549 < baseStart_475549 := by decide
  rcases family_descends (prefixWord ++ tailWord_475549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475605 : List Nat := [1, 3, 2, 3, 1, 4, 7]
def baseStart_475605 : Nat := 118140960795 + 475605 * 2 ^ 59
def prefixEnd_475605 : Nat := 4983230072969 + 3 ^ 40 * 475605 * 2
def baseEnd_475605 : Nat := 12059948971936638367913

theorem tailTrace_475605 : CollatzResearch.WordTrace tailWord_475605 prefixEnd_475605 12059948971936638367913 := by
  unfold tailWord_475605
  simp only [CollatzResearch.WordTrace]
  refine ⟨17346739441971786712308269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11564492961314524474872179 17346739441971786712308269)
  ·
    refine ⟨6505027290739420017115601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17346739441971786712308269 6505027290739420017115601)
    ·
      refine ⟨4878770468054565012836701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6505027290739420017115601 4878770468054565012836701)
      ·
        refine ⟨1829538925520461879813763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4878770468054565012836701 1829538925520461879813763)
        ·
          refine ⟨2744308388280692819720645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1829538925520461879813763 2744308388280692819720645)
          ·
            refine ⟨514557822802629903697621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2744308388280692819720645 514557822802629903697621)
            ·
              refine ⟨12059948971936638367913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 514557822802629903697621 12059948971936638367913)
              ·
                rfl

theorem cell21_475605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 7].length) (baseStart_475605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_475605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_475605 prefixEnd_475605 := by exact prefixLift 475605
  have htrace : WordTrace (prefixWord ++ tailWord_475605) baseStart_475605 baseEnd_475605 := by
    simpa [prefixWord, tailWord_475605, baseEnd_475605] using wordTrace_append hprefix tailTrace_475605
  have hstable : (prefixWord ++ tailWord_475605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475605).length < 2 ^ (prefixWord ++ tailWord_475605).sum := by decide
  have hdescent : baseEnd_475605 < baseStart_475605 := by decide
  rcases family_descends (prefixWord ++ tailWord_475605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475712 : List Nat := [2, 1, 1, 2, 2, 2, 3, 5, 3]
def baseStart_475712 : Nat := 118140960795 + 475712 * 2 ^ 59
def prefixEnd_475712 : Nat := 4983230072969 + 3 ^ 40 * 475712 * 2
def baseEnd_475712 : Nat := 108563959605221337027665

theorem tailTrace_475712 : CollatzResearch.WordTrace tailWord_475712 prefixEnd_475712 108563959605221337027665 := by
  unfold tailWord_475712
  simp only [CollatzResearch.WordTrace]
  refine ⟨8675321026292071993226695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11567094701722762657635593 8675321026292071993226695)
  ·
    refine ⟨13012981539438107989840043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8675321026292071993226695 13012981539438107989840043)
    ·
      refine ⟨19519472309157161984760065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13012981539438107989840043 19519472309157161984760065)
      ·
        refine ⟨14639604231867871488570049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19519472309157161984760065 14639604231867871488570049)
        ·
          refine ⟨10979703173900903616427537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14639604231867871488570049 10979703173900903616427537)
          ·
            refine ⟨8234777380425677712320653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10979703173900903616427537 8234777380425677712320653)
            ·
              refine ⟨3088041517659629142120245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8234777380425677712320653 3088041517659629142120245)
              ·
                refine ⟨289503892280590232073773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3088041517659629142120245 289503892280590232073773)
                ·
                  refine ⟨108563959605221337027665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 289503892280590232073773 108563959605221337027665)
                  ·
                    rfl

theorem cell21_475712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 5, 3].length) (baseStart_475712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_475712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_475712 prefixEnd_475712 := by exact prefixLift 475712
  have htrace : WordTrace (prefixWord ++ tailWord_475712) baseStart_475712 baseEnd_475712 := by
    simpa [prefixWord, tailWord_475712, baseEnd_475712] using wordTrace_append hprefix tailTrace_475712
  have hstable : (prefixWord ++ tailWord_475712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475712).length < 2 ^ (prefixWord ++ tailWord_475712).sum := by decide
  have hdescent : baseEnd_475712 < baseStart_475712 := by decide
  rcases family_descends (prefixWord ++ tailWord_475712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475757 : List Nat := [1, 5, 1, 1, 3, 2, 1, 7]
def baseStart_475757 : Nat := 118140960795 + 475757 * 2 ^ 59
def prefixEnd_475757 : Nat := 4983230072969 + 3 ^ 40 * 475757 * 2
def baseEnd_475757 : Nat := 36191409739437086259191

theorem tailTrace_475757 : CollatzResearch.WordTrace tailWord_475757 prefixEnd_475757 36191409739437086259191 := by
  unfold tailWord_475757
  simp only [CollatzResearch.WordTrace]
  refine ⟨17352283337421116671841525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11568188891614077781227683 17352283337421116671841525)
  ·
    refine ⟨1626776562883229687985143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17352283337421116671841525 1626776562883229687985143)
    ·
      refine ⟨2440164844324844531977715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1626776562883229687985143 2440164844324844531977715)
      ·
        refine ⟨3660247266487266797966573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2440164844324844531977715 3660247266487266797966573)
        ·
          refine ⟨1372592724932725049237465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3660247266487266797966573 1372592724932725049237465)
          ·
            refine ⟨1029444543699543786928099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1372592724932725049237465 1029444543699543786928099)
            ·
              refine ⟨1544166815549315680392149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1029444543699543786928099 1544166815549315680392149)
              ·
                refine ⟨36191409739437086259191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1544166815549315680392149 36191409739437086259191)
                ·
                  rfl

theorem cell21_475757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 7].length) (baseStart_475757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_475757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_475757 prefixEnd_475757 := by exact prefixLift 475757
  have htrace : WordTrace (prefixWord ++ tailWord_475757) baseStart_475757 baseEnd_475757 := by
    simpa [prefixWord, tailWord_475757, baseEnd_475757] using wordTrace_append hprefix tailTrace_475757
  have hstable : (prefixWord ++ tailWord_475757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475757).length < 2 ^ (prefixWord ++ tailWord_475757).sum := by decide
  have hdescent : baseEnd_475757 < baseStart_475757 := by decide
  rcases family_descends (prefixWord ++ tailWord_475757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475937 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 8]
def baseStart_475937 : Nat := 118140960795 + 475937 * 2 ^ 59
def prefixEnd_475937 : Nat := 4983230072969 + 3 ^ 40 * 475937 * 2
def baseEnd_475937 : Nat := 108615307670670945777205

theorem tailTrace_475937 : CollatzResearch.WordTrace tailWord_475937 prefixEnd_475937 108615307670670945777205 := by
  unfold tailWord_475937
  simp only [CollatzResearch.WordTrace]
  refine ⟨17358848476769007413394065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11572565651179338275596043 17358848476769007413394065)
  ·
    refine ⟨13019136357576755560045549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17358848476769007413394065 13019136357576755560045549)
    ·
      refine ⟨4882176134091283335017081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13019136357576755560045549 4882176134091283335017081)
      ·
        refine ⟨3661632100568462501262811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4882176134091283335017081 3661632100568462501262811)
        ·
          refine ⟨5492448150852693751894217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3661632100568462501262811 5492448150852693751894217)
          ·
            refine ⟨4119336113139520313920663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5492448150852693751894217 4119336113139520313920663)
            ·
              refine ⟨6179004169709280470880995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4119336113139520313920663 6179004169709280470880995)
              ·
                refine ⟨9268506254563920706321493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6179004169709280470880995 9268506254563920706321493)
                ·
                  refine ⟨108615307670670945777205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9268506254563920706321493 108615307670670945777205)
                  ·
                    rfl

theorem cell21_475937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 8].length) (baseStart_475937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_475937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_475937 prefixEnd_475937 := by exact prefixLift 475937
  have htrace : WordTrace (prefixWord ++ tailWord_475937) baseStart_475937 baseEnd_475937 := by
    simpa [prefixWord, tailWord_475937, baseEnd_475937] using wordTrace_append hprefix tailTrace_475937
  have hstable : (prefixWord ++ tailWord_475937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475937).length < 2 ^ (prefixWord ++ tailWord_475937).sum := by decide
  have hdescent : baseEnd_475937 < baseStart_475937 := by decide
  rcases family_descends (prefixWord ++ tailWord_475937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475954 : List Nat := [3, 2, 1, 1, 3, 1, 2, 4, 4]
def baseStart_475954 : Nat := 118140960795 + 475954 * 2 ^ 59
def prefixEnd_475954 : Nat := 4983230072969 + 3 ^ 40 * 475954 * 2
def baseEnd_475954 : Nat := 108619187302282693993837

theorem tailTrace_475954 : CollatzResearch.WordTrace tailWord_475954 prefixEnd_475954 108619187302282693993837 := by
  unfold tailWord_475954
  simp only [CollatzResearch.WordTrace]
  refine ⟨4339867129426854829190729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11572979011804946211175277 4339867129426854829190729)
  ·
    refine ⟨3254900347070141121893047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4339867129426854829190729 3254900347070141121893047)
    ·
      refine ⟨4882350520605211682839571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3254900347070141121893047 4882350520605211682839571)
      ·
        refine ⟨7323525780907817524259357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4882350520605211682839571 7323525780907817524259357)
        ·
          refine ⟨2746322167840431571597259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7323525780907817524259357 2746322167840431571597259)
          ·
            refine ⟨4119483251760647357395889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2746322167840431571597259 4119483251760647357395889)
            ·
              refine ⟨3089612438820485518046917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4119483251760647357395889 3089612438820485518046917)
              ·
                refine ⟨579302332278841034633797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3089612438820485518046917 579302332278841034633797)
                ·
                  refine ⟨108619187302282693993837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 579302332278841034633797 108619187302282693993837)
                  ·
                    rfl

theorem cell21_475954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_475954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_475954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_475954 prefixEnd_475954 := by exact prefixLift 475954
  have htrace : WordTrace (prefixWord ++ tailWord_475954) baseStart_475954 baseEnd_475954 := by
    simpa [prefixWord, tailWord_475954, baseEnd_475954] using wordTrace_append hprefix tailTrace_475954
  have hstable : (prefixWord ++ tailWord_475954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475954).length < 2 ^ (prefixWord ++ tailWord_475954).sum := by decide
  have hdescent : baseEnd_475954 < baseStart_475954 := by decide
  rcases family_descends (prefixWord ++ tailWord_475954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476050 : List Nat := [3, 2, 3, 2, 2, 1, 2, 3, 3]
def baseStart_476050 : Nat := 118140960795 + 476050 * 2 ^ 59
def prefixEnd_476050 : Nat := 4983230072969 + 3 ^ 40 * 476050 * 2
def baseEnd_476050 : Nat := 108641095810207860393641

theorem tailTrace_476050 : CollatzResearch.WordTrace tailWord_476050 prefixEnd_476050 108641095810207860393641 := by
  unfold tailWord_476050
  simp only [CollatzResearch.WordTrace]
  refine ⟨4340742481339906928064401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11575313283573085141505069 4340742481339906928064401)
  ·
    refine ⟨3255556861004930196048301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4340742481339906928064401 3255556861004930196048301)
    ·
      refine ⟨1220833822876848823518113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3255556861004930196048301 1220833822876848823518113)
      ·
        refine ⟨915625367157636617638585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1220833822876848823518113 915625367157636617638585)
        ·
          refine ⟨686719025368227463228939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 915625367157636617638585 686719025368227463228939)
          ·
            refine ⟨1030078538052341194843409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686719025368227463228939 1030078538052341194843409)
            ·
              refine ⟨772558903539255896132557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1030078538052341194843409 772558903539255896132557)
              ·
                refine ⟨289709588827220961049709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 772558903539255896132557 289709588827220961049709)
                ·
                  refine ⟨108641095810207860393641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 289709588827220961049709 108641095810207860393641)
                  ·
                    rfl

theorem cell21_476050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_476050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_476050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_476050 prefixEnd_476050 := by exact prefixLift 476050
  have htrace : WordTrace (prefixWord ++ tailWord_476050) baseStart_476050 baseEnd_476050 := by
    simpa [prefixWord, tailWord_476050, baseEnd_476050] using wordTrace_append hprefix tailTrace_476050
  have hstable : (prefixWord ++ tailWord_476050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476050).length < 2 ^ (prefixWord ++ tailWord_476050).sum := by decide
  have hdescent : baseEnd_476050 < baseStart_476050 := by decide
  rcases family_descends (prefixWord ++ tailWord_476050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476120 : List Nat := [2, 1, 2, 2, 2, 5, 7]
def baseStart_476120 : Nat := 118140960795 + 476120 * 2 ^ 59
def prefixEnd_476120 : Nat := 4983230072969 + 3 ^ 40 * 476120 * 2
def baseEnd_476120 : Nat := 12073007862655921580759

theorem tailTrace_476120 : CollatzResearch.WordTrace tailWord_476120 prefixEnd_476120 12073007862655921580759 := by
  unfold tailWord_476120
  simp only [CollatzResearch.WordTrace]
  refine ⟨8682761517553014833652907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11577015356737353111537209 8682761517553014833652907)
  ·
    refine ⟨13024142276329522250479361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8682761517553014833652907 13024142276329522250479361)
    ·
      refine ⟨9768106707247141687859521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13024142276329522250479361 9768106707247141687859521)
      ·
        refine ⟨7326080030435356265894641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9768106707247141687859521 7326080030435356265894641)
        ·
          refine ⟨5494560022826517199420981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7326080030435356265894641 5494560022826517199420981)
          ·
            refine ⟨515115002139985987445717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5494560022826517199420981 515115002139985987445717)
            ·
              refine ⟨12073007862655921580759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 515115002139985987445717 12073007862655921580759)
              ·
                rfl

theorem cell21_476120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 7].length) (baseStart_476120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_476120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_476120 prefixEnd_476120 := by exact prefixLift 476120
  have htrace : WordTrace (prefixWord ++ tailWord_476120) baseStart_476120 baseEnd_476120 := by
    simpa [prefixWord, tailWord_476120, baseEnd_476120] using wordTrace_append hprefix tailTrace_476120
  have hstable : (prefixWord ++ tailWord_476120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476120).length < 2 ^ (prefixWord ++ tailWord_476120).sum := by decide
  have hdescent : baseEnd_476120 < baseStart_476120 := by decide
  rcases family_descends (prefixWord ++ tailWord_476120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476199 : List Nat := [1, 1, 7, 1, 1, 1, 2, 3, 4]
def baseStart_476199 : Nat := 118140960795 + 476199 * 2 ^ 59
def prefixEnd_476199 : Nat := 4983230072969 + 3 ^ 40 * 476199 * 2
def baseEnd_476199 : Nat := 108675099640216712410003

theorem tailTrace_476199 : CollatzResearch.WordTrace tailWord_476199 prefixEnd_476199 108675099640216712410003 := by
  unfold tailWord_476199
  simp only [CollatzResearch.WordTrace]
  refine ⟨17368404401819826159431651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11578936267879884106287767 17368404401819826159431651)
  ·
    refine ⟨26052606602729739239147477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17368404401819826159431651 26052606602729739239147477)
    ·
      refine ⟨610607967251478263417519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 26052606602729739239147477 610607967251478263417519)
      ·
        refine ⟨915911950877217395126279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610607967251478263417519 915911950877217395126279)
        ·
          refine ⟨1373867926315826092689419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 915911950877217395126279 1373867926315826092689419)
          ·
            refine ⟨2060801889473739139034129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373867926315826092689419 2060801889473739139034129)
            ·
              refine ⟨1545601417105304354275597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2060801889473739139034129 1545601417105304354275597)
              ·
                refine ⟨579600531414489132853349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1545601417105304354275597 579600531414489132853349)
                ·
                  refine ⟨108675099640216712410003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 579600531414489132853349 108675099640216712410003)
                  ·
                    rfl

theorem cell21_476199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 4].length) (baseStart_476199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_476199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_476199 prefixEnd_476199 := by exact prefixLift 476199
  have htrace : WordTrace (prefixWord ++ tailWord_476199) baseStart_476199 baseEnd_476199 := by
    simpa [prefixWord, tailWord_476199, baseEnd_476199] using wordTrace_append hprefix tailTrace_476199
  have hstable : (prefixWord ++ tailWord_476199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476199).length < 2 ^ (prefixWord ++ tailWord_476199).sum := by decide
  have hdescent : baseEnd_476199 < baseStart_476199 := by decide
  rcases family_descends (prefixWord ++ tailWord_476199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476244 : List Nat := [2, 4, 1, 1, 1, 1, 4, 4, 3]
def baseStart_476244 : Nat := 118140960795 + 476244 * 2 ^ 59
def prefixEnd_476244 : Nat := 4983230072969 + 3 ^ 40 * 476244 * 2
def baseEnd_476244 : Nat := 108685369253306634159911

theorem tailTrace_476244 : CollatzResearch.WordTrace tailWord_476244 prefixEnd_476244 108685369253306634159911 := by
  unfold tailWord_476244
  simp only [CollatzResearch.WordTrace]
  refine ⟨8685022843328399422409893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11580030457771199229879857 8685022843328399422409893)
  ·
    refine ⟨1628441783124074891701855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8685022843328399422409893 1628441783124074891701855)
    ·
      refine ⟨2442662674686112337552783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1628441783124074891701855 2442662674686112337552783)
      ·
        refine ⟨3663994012029168506329175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2442662674686112337552783 3663994012029168506329175)
        ·
          refine ⟨5495991018043752759493763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3663994012029168506329175 5495991018043752759493763)
          ·
            refine ⟨8243986527065629139240645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5495991018043752759493763 8243986527065629139240645)
            ·
              refine ⟨1545747473824805463607621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8243986527065629139240645 1545747473824805463607621)
              ·
                refine ⟨289827651342151024426429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1545747473824805463607621 289827651342151024426429)
                ·
                  refine ⟨108685369253306634159911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 289827651342151024426429 108685369253306634159911)
                  ·
                    rfl

theorem cell21_476244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_476244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_476244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_476244 prefixEnd_476244 := by exact prefixLift 476244
  have htrace : WordTrace (prefixWord ++ tailWord_476244) baseStart_476244 baseEnd_476244 := by
    simpa [prefixWord, tailWord_476244, baseEnd_476244] using wordTrace_append hprefix tailTrace_476244
  have hstable : (prefixWord ++ tailWord_476244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476244).length < 2 ^ (prefixWord ++ tailWord_476244).sum := by decide
  have hdescent : baseEnd_476244 < baseStart_476244 := by decide
  rcases family_descends (prefixWord ++ tailWord_476244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476255 : List Nat := [1, 1, 2, 3, 1, 1, 4, 8]
def baseStart_476255 : Nat := 118140960795 + 476255 * 2 ^ 59
def prefixEnd_476255 : Nat := 4983230072969 + 3 ^ 40 * 476255 * 2
def baseEnd_476255 : Nat := 36229293201057686492185

theorem tailTrace_476255 : CollatzResearch.WordTrace tailWord_476255 prefixEnd_476255 36229293201057686492185 := by
  unfold tailWord_476255
  simp only [CollatzResearch.WordTrace]
  refine ⟨17370446889616947723470219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11580297926411298482313479 17370446889616947723470219)
  ·
    refine ⟨26055670334425421585205329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17370446889616947723470219 26055670334425421585205329)
    ·
      refine ⟨19541752750819066188903997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26055670334425421585205329 19541752750819066188903997)
      ·
        refine ⟨7328157281557149820838999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19541752750819066188903997 7328157281557149820838999)
        ·
          refine ⟨10992235922335724731258499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7328157281557149820838999 10992235922335724731258499)
          ·
            refine ⟨16488353883503587096887749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10992235922335724731258499 16488353883503587096887749)
            ·
              refine ⟨3091566353156922580666453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16488353883503587096887749 3091566353156922580666453)
              ·
                refine ⟨36229293201057686492185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3091566353156922580666453 36229293201057686492185)
                ·
                  rfl

theorem cell21_476255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 8].length) (baseStart_476255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_476255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_476255 prefixEnd_476255 := by exact prefixLift 476255
  have htrace : WordTrace (prefixWord ++ tailWord_476255) baseStart_476255 baseEnd_476255 := by
    simpa [prefixWord, tailWord_476255, baseEnd_476255] using wordTrace_append hprefix tailTrace_476255
  have hstable : (prefixWord ++ tailWord_476255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476255).length < 2 ^ (prefixWord ++ tailWord_476255).sum := by decide
  have hdescent : baseEnd_476255 < baseStart_476255 := by decide
  rcases family_descends (prefixWord ++ tailWord_476255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476396 : List Nat := [2, 2, 1, 1, 2, 5, 2, 3, 3]
def baseStart_476396 : Nat := 118140960795 + 476396 * 2 ^ 59
def prefixEnd_476396 : Nat := 4983230072969 + 3 ^ 40 * 476396 * 2
def baseEnd_476396 : Nat := 108720057724188147626267

theorem tailTrace_476396 : CollatzResearch.WordTrace tailWord_476396 prefixEnd_476396 108720057724188147626267 := by
  unfold tailWord_476396
  simp only [CollatzResearch.WordTrace]
  refine ⟨8687794791053064402176521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11583726388070752536235361 8687794791053064402176521)
  ·
    refine ⟨6515846093289798301632391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8687794791053064402176521 6515846093289798301632391)
    ·
      refine ⟨9773769139934697452448587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6515846093289798301632391 9773769139934697452448587)
      ·
        refine ⟨14660653709902046178672881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9773769139934697452448587 14660653709902046178672881)
        ·
          refine ⟨10995490282426534634004661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14660653709902046178672881 10995490282426534634004661)
          ·
            refine ⟨1030827213977487621937937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10995490282426534634004661 1030827213977487621937937)
            ·
              refine ⟨773120410483115716453453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1030827213977487621937937 773120410483115716453453)
              ·
                refine ⟨289920153931168393670045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 773120410483115716453453 289920153931168393670045)
                ·
                  refine ⟨108720057724188147626267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 289920153931168393670045 108720057724188147626267)
                  ·
                    rfl

theorem cell21_476396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3, 3].length) (baseStart_476396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_476396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_476396 prefixEnd_476396 := by exact prefixLift 476396
  have htrace : WordTrace (prefixWord ++ tailWord_476396) baseStart_476396 baseEnd_476396 := by
    simpa [prefixWord, tailWord_476396, baseEnd_476396] using wordTrace_append hprefix tailTrace_476396
  have hstable : (prefixWord ++ tailWord_476396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476396).length < 2 ^ (prefixWord ++ tailWord_476396).sum := by decide
  have hdescent : baseEnd_476396 < baseStart_476396 := by decide
  rcases family_descends (prefixWord ++ tailWord_476396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476469 : List Nat := [1, 3, 3, 1, 2, 2, 2, 1, 6]
def baseStart_476469 : Nat := 118140960795 + 476469 * 2 ^ 59
def prefixEnd_476469 : Nat := 4983230072969 + 3 ^ 40 * 476469 * 2
def baseEnd_476469 : Nat := 108736717318756242909451

theorem tailTrace_476469 : CollatzResearch.WordTrace tailWord_476469 prefixEnd_476469 108736717318756242909451 := by
  unfold tailWord_476469
  simp only [CollatzResearch.WordTrace]
  refine ⟨17378252110841662271760461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11585501407227774847840307 17378252110841662271760461)
  ·
    refine ⟨6516844541565623351910173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17378252110841662271760461 6516844541565623351910173)
    ·
      refine ⟨2443816703087108756966315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6516844541565623351910173 2443816703087108756966315)
      ·
        refine ⟨3665725054630663135449473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2443816703087108756966315 3665725054630663135449473)
        ·
          refine ⟨2749293790972997351587105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3665725054630663135449473 2749293790972997351587105)
          ·
            refine ⟨2061970343229748013690329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2749293790972997351587105 2061970343229748013690329)
            ·
              refine ⟨1546477757422311010267747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2061970343229748013690329 1546477757422311010267747)
              ·
                refine ⟨2319716636133466515401621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1546477757422311010267747 2319716636133466515401621)
                ·
                  refine ⟨108736717318756242909451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2319716636133466515401621 108736717318756242909451)
                  ·
                    rfl

theorem cell21_476469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_476469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_476469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_476469 prefixEnd_476469 := by exact prefixLift 476469
  have htrace : WordTrace (prefixWord ++ tailWord_476469) baseStart_476469 baseEnd_476469 := by
    simpa [prefixWord, tailWord_476469, baseEnd_476469] using wordTrace_append hprefix tailTrace_476469
  have hstable : (prefixWord ++ tailWord_476469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476469).length < 2 ^ (prefixWord ++ tailWord_476469).sum := by decide
  have hdescent : baseEnd_476469 < baseStart_476469 := by decide
  rcases family_descends (prefixWord ++ tailWord_476469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476680 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 8]
def baseStart_476680 : Nat := 118140960795 + 476680 * 2 ^ 59
def prefixEnd_476680 : Nat := 4983230072969 + 3 ^ 40 * 476680 * 2
def baseEnd_476680 : Nat := 108784870393466764892353

theorem tailTrace_476680 : CollatzResearch.WordTrace tailWord_476680 prefixEnd_476680 108784870393466764892353 := by
  unfold tailWord_476680
  simp only [CollatzResearch.WordTrace]
  refine ⟨8692973956538622653845747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11590631942051496871794329 8692973956538622653845747)
  ·
    refine ⟨13039460934807933980768621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8692973956538622653845747 13039460934807933980768621)
    ·
      refine ⟨4889797850552975242788233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13039460934807933980768621 4889797850552975242788233)
      ·
        refine ⟨3667348387914731432091175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4889797850552975242788233 3667348387914731432091175)
        ·
          refine ⟨5501022581872097148136763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3667348387914731432091175 5501022581872097148136763)
          ·
            refine ⟨8251533872808145722205145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5501022581872097148136763 8251533872808145722205145)
            ·
              refine ⟨6188650404606109291653859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8251533872808145722205145 6188650404606109291653859)
              ·
                refine ⟨9282975606909163937480789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6188650404606109291653859 9282975606909163937480789)
                ·
                  refine ⟨108784870393466764892353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9282975606909163937480789 108784870393466764892353)
                  ·
                    rfl

theorem cell21_476680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 8].length) (baseStart_476680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_476680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_476680 prefixEnd_476680 := by exact prefixLift 476680
  have htrace : WordTrace (prefixWord ++ tailWord_476680) baseStart_476680 baseEnd_476680 := by
    simpa [prefixWord, tailWord_476680, baseEnd_476680] using wordTrace_append hprefix tailTrace_476680
  have hstable : (prefixWord ++ tailWord_476680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476680).length < 2 ^ (prefixWord ++ tailWord_476680).sum := by decide
  have hdescent : baseEnd_476680 < baseStart_476680 := by decide
  rcases family_descends (prefixWord ++ tailWord_476680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476728 : List Nat := [2, 1, 2, 1, 4, 3, 3, 5]
def baseStart_476728 : Nat := 118140960795 + 476728 * 2 ^ 59
def prefixEnd_476728 : Nat := 4983230072969 + 3 ^ 40 * 476728 * 2
def baseEnd_476728 : Nat := 36265274882476449364085

theorem tailTrace_476728 : CollatzResearch.WordTrace tailWord_476728 prefixEnd_476728 36265274882476449364085 := by
  unfold tailWord_476728
  simp only [CollatzResearch.WordTrace]
  refine ⟨8693849308451674752719419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11591799077935566336959225 8693849308451674752719419)
  ·
    refine ⟨13040773962677512129079129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8693849308451674752719419 13040773962677512129079129)
    ·
      refine ⟨9780580472008134096809347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13040773962677512129079129 9780580472008134096809347)
      ·
        refine ⟨14670870708012201145214021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9780580472008134096809347 14670870708012201145214021)
        ·
          refine ⟨2750788257752287714727629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14670870708012201145214021 2750788257752287714727629)
          ·
            refine ⟨1031545596657107893022861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2750788257752287714727629 1031545596657107893022861)
            ·
              refine ⟨386829598746415459883573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1031545596657107893022861 386829598746415459883573)
              ·
                refine ⟨36265274882476449364085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 386829598746415459883573 36265274882476449364085)
                ·
                  rfl

theorem cell21_476728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 5].length) (baseStart_476728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_476728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_476728 prefixEnd_476728 := by exact prefixLift 476728
  have htrace : WordTrace (prefixWord ++ tailWord_476728) baseStart_476728 baseEnd_476728 := by
    simpa [prefixWord, tailWord_476728, baseEnd_476728] using wordTrace_append hprefix tailTrace_476728
  have hstable : (prefixWord ++ tailWord_476728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476728).length < 2 ^ (prefixWord ++ tailWord_476728).sum := by decide
  have hdescent : baseEnd_476728 < baseStart_476728 := by decide
  rcases family_descends (prefixWord ++ tailWord_476728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476759 : List Nat := [1, 1, 3, 2, 2, 3, 2, 4, 3]
def baseStart_476759 : Nat := 118140960795 + 476759 * 2 ^ 59
def prefixEnd_476759 : Nat := 4983230072969 + 3 ^ 40 * 476759 * 2
def baseEnd_476759 : Nat := 108802899269780183075525

theorem tailTrace_476759 : CollatzResearch.WordTrace tailWord_476759 prefixEnd_476759 108802899269780183075525 := by
  unfold tailWord_476759
  simp only [CollatzResearch.WordTrace]
  refine ⟨17388829279791041799817331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11592552853194027866544887 17388829279791041799817331)
  ·
    refine ⟨26083243919686562699725997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17388829279791041799817331 26083243919686562699725997)
    ·
      refine ⟨9781216469882461012397249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26083243919686562699725997 9781216469882461012397249)
      ·
        refine ⟨7335912352411845759297937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9781216469882461012397249 7335912352411845759297937)
        ·
          refine ⟨5501934264308884319473453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7335912352411845759297937 5501934264308884319473453)
          ·
            refine ⟨2063225349115831619802545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5501934264308884319473453 2063225349115831619802545)
            ·
              refine ⟨1547419011836873714851909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2063225349115831619802545 1547419011836873714851909)
              ·
                refine ⟨290141064719413821534733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1547419011836873714851909 290141064719413821534733)
                ·
                  refine ⟨108802899269780183075525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 290141064719413821534733 108802899269780183075525)
                  ·
                    rfl

theorem cell21_476759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 4, 3].length) (baseStart_476759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_476759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_476759 prefixEnd_476759 := by exact prefixLift 476759
  have htrace : WordTrace (prefixWord ++ tailWord_476759) baseStart_476759 baseEnd_476759 := by
    simpa [prefixWord, tailWord_476759, baseEnd_476759] using wordTrace_append hprefix tailTrace_476759
  have hstable : (prefixWord ++ tailWord_476759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476759).length < 2 ^ (prefixWord ++ tailWord_476759).sum := by decide
  have hdescent : baseEnd_476759 < baseStart_476759 := by decide
  rcases family_descends (prefixWord ++ tailWord_476759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476804 : List Nat := [2, 3, 2, 1, 4, 2, 7]
def baseStart_476804 : Nat := 118140960795 + 476804 * 2 ^ 59
def prefixEnd_476804 : Nat := 4983230072969 + 3 ^ 40 * 476804 * 2
def baseEnd_476804 : Nat := 12090352098096678313937

theorem tailTrace_476804 : CollatzResearch.WordTrace tailWord_476804 prefixEnd_476804 12090352098096678313937 := by
  unfold tailWord_476804
  simp only [CollatzResearch.WordTrace]
  refine ⟨8695235282314007242602733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11593647043085342990136977 8695235282314007242602733)
  ·
    refine ⟨3260713230867752715976025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8695235282314007242602733 3260713230867752715976025)
    ·
      refine ⟨2445534923150814536982019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3260713230867752715976025 2445534923150814536982019)
      ·
        refine ⟨3668302384726221805473029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2445534923150814536982019 3668302384726221805473029)
        ·
          refine ⟨687806697136166588526193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3668302384726221805473029 687806697136166588526193)
          ·
            refine ⟨515855022852124941394645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 687806697136166588526193 515855022852124941394645)
            ·
              refine ⟨12090352098096678313937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 515855022852124941394645 12090352098096678313937)
              ·
                rfl

theorem cell21_476804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 7].length) (baseStart_476804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_476804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_476804 prefixEnd_476804 := by exact prefixLift 476804
  have htrace : WordTrace (prefixWord ++ tailWord_476804) baseStart_476804 baseEnd_476804 := by
    simpa [prefixWord, tailWord_476804, baseEnd_476804] using wordTrace_append hprefix tailTrace_476804
  have hstable : (prefixWord ++ tailWord_476804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476804).length < 2 ^ (prefixWord ++ tailWord_476804).sum := by decide
  have hdescent : baseEnd_476804 < baseStart_476804 := by decide
  rcases family_descends (prefixWord ++ tailWord_476804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476911 : List Nat := [1, 1, 2, 1, 5, 1, 4, 3, 3]
def baseStart_476911 : Nat := 118140960795 + 476911 * 2 ^ 59
def prefixEnd_476911 : Nat := 4983230072969 + 3 ^ 40 * 476911 * 2
def baseEnd_476911 : Nat := 108837587740661696541881

theorem tailTrace_476911 : CollatzResearch.WordTrace tailWord_476911 prefixEnd_476911 108837587740661696541881 := by
  unfold tailWord_476911
  simp only [CollatzResearch.WordTrace]
  refine ⟨17394373175240371759350587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11596248783493581172900391 17394373175240371759350587)
  ·
    refine ⟨26091559762860557639025881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17394373175240371759350587 26091559762860557639025881)
    ·
      refine ⟨19568669822145418229269411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26091559762860557639025881 19568669822145418229269411)
      ·
        refine ⟨29353004733218127343904117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19568669822145418229269411 29353004733218127343904117)
        ·
          refine ⟨2751844193739199438491011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29353004733218127343904117 2751844193739199438491011)
          ·
            refine ⟨4127766290608799157736517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2751844193739199438491011 4127766290608799157736517)
            ·
              refine ⟨773956179489149842075597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4127766290608799157736517 773956179489149842075597)
              ·
                refine ⟨290233567308431190778349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 773956179489149842075597 290233567308431190778349)
                ·
                  refine ⟨108837587740661696541881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 290233567308431190778349 108837587740661696541881)
                  ·
                    rfl

theorem cell21_476911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 3, 3].length) (baseStart_476911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_476911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_476911 prefixEnd_476911 := by exact prefixLift 476911
  have htrace : WordTrace (prefixWord ++ tailWord_476911) baseStart_476911 baseEnd_476911 := by
    simpa [prefixWord, tailWord_476911, baseEnd_476911] using wordTrace_append hprefix tailTrace_476911
  have hstable : (prefixWord ++ tailWord_476911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476911).length < 2 ^ (prefixWord ++ tailWord_476911).sum := by decide
  have hdescent : baseEnd_476911 < baseStart_476911 := by decide
  rcases family_descends (prefixWord ++ tailWord_476911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476948 : List Nat := [2, 4, 4, 1, 2, 1, 2, 5]
def baseStart_476948 : Nat := 118140960795 + 476948 * 2 ^ 59
def prefixEnd_476948 : Nat := 4983230072969 + 3 ^ 40 * 476948 * 2
def baseEnd_476948 : Nat := 36282010548252618141713

theorem tailTrace_476948 : CollatzResearch.WordTrace tailWord_476948 prefixEnd_476948 36282010548252618141713 := by
  unfold tailWord_476948
  simp only [CollatzResearch.WordTrace]
  refine ⟨8697861338053163539223749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11597148450737551385631665 8697861338053163539223749)
  ·
    refine ⟨1630849000884968163604453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8697861338053163539223749 1630849000884968163604453)
    ·
      refine ⟨305784187665931530675835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1630849000884968163604453 305784187665931530675835)
      ·
        refine ⟨458676281498897296013753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305784187665931530675835 458676281498897296013753)
        ·
          refine ⟨344007211124172972010315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 458676281498897296013753 344007211124172972010315)
          ·
            refine ⟨516010816686259458015473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344007211124172972010315 516010816686259458015473)
            ·
              refine ⟨387008112514694593511605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 516010816686259458015473 387008112514694593511605)
              ·
                refine ⟨36282010548252618141713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 387008112514694593511605 36282010548252618141713)
                ·
                  rfl

theorem cell21_476948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 5].length) (baseStart_476948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_476948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_476948 prefixEnd_476948 := by exact prefixLift 476948
  have htrace : WordTrace (prefixWord ++ tailWord_476948) baseStart_476948 baseEnd_476948 := by
    simpa [prefixWord, tailWord_476948, baseEnd_476948] using wordTrace_append hprefix tailTrace_476948
  have hstable : (prefixWord ++ tailWord_476948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476948).length < 2 ^ (prefixWord ++ tailWord_476948).sum := by decide
  have hdescent : baseEnd_476948 < baseStart_476948 := by decide
  rcases family_descends (prefixWord ++ tailWord_476948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476984 : List Nat := [2, 1, 2, 1, 3, 3, 2, 1, 6]
def baseStart_476984 : Nat := 118140960795 + 476984 * 2 ^ 59
def prefixEnd_476984 : Nat := 4983230072969 + 3 ^ 40 * 476984 * 2
def baseEnd_476984 : Nat := 108854247335229791825065

theorem tailTrace_476984 : CollatzResearch.WordTrace tailWord_476984 prefixEnd_476984 108854247335229791825065 := by
  unfold tailWord_476984
  simp only [CollatzResearch.WordTrace]
  refine ⟨8698517851987952613379003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11598023802650603484505337 8698517851987952613379003)
  ·
    refine ⟨13047776777981928920068505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8698517851987952613379003 13047776777981928920068505)
    ·
      refine ⟨9785832583486446690051379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13047776777981928920068505 9785832583486446690051379)
      ·
        refine ⟨14678748875229670035077069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9785832583486446690051379 14678748875229670035077069)
        ·
          refine ⟨5504530828211126263153901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14678748875229670035077069 5504530828211126263153901)
          ·
            refine ⟨2064199060579172348682713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5504530828211126263153901 2064199060579172348682713)
            ·
              refine ⟨1548149295434379261512035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2064199060579172348682713 1548149295434379261512035)
              ·
                refine ⟨2322223943151568892268053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1548149295434379261512035 2322223943151568892268053)
                ·
                  refine ⟨108854247335229791825065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2322223943151568892268053 108854247335229791825065)
                  ·
                    rfl

theorem cell21_476984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 6].length) (baseStart_476984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_476984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_476984 prefixEnd_476984 := by exact prefixLift 476984
  have htrace : WordTrace (prefixWord ++ tailWord_476984) baseStart_476984 baseEnd_476984 := by
    simpa [prefixWord, tailWord_476984, baseEnd_476984] using wordTrace_append hprefix tailTrace_476984
  have hstable : (prefixWord ++ tailWord_476984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476984).length < 2 ^ (prefixWord ++ tailWord_476984).sum := by decide
  have hdescent : baseEnd_476984 < baseStart_476984 := by decide
  rcases family_descends (prefixWord ++ tailWord_476984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477181 : List Nat := [1, 4, 1, 1, 1, 2, 2, 4, 5]
def baseStart_477181 : Nat := 118140960795 + 477181 * 2 ^ 59
def prefixEnd_477181 : Nat := 4983230072969 + 3 ^ 40 * 477181 * 2
def baseEnd_477181 : Nat := 108899205419201227041329

theorem tailTrace_477181 : CollatzResearch.WordTrace tailWord_477181 prefixEnd_477181 108899205419201227041329 := by
  unfold tailWord_477181
  simp only [CollatzResearch.WordTrace]
  refine ⟨17404220884262207871679397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11602813922841471914452931 17404220884262207871679397)
  ·
    refine ⟨3263291415799163975939887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17404220884262207871679397 3263291415799163975939887)
    ·
      refine ⟨4894937123698745963909831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3263291415799163975939887 4894937123698745963909831)
      ·
        refine ⟨7342405685548118945864747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4894937123698745963909831 7342405685548118945864747)
        ·
          refine ⟨11013608528322178418797121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7342405685548118945864747 11013608528322178418797121)
          ·
            refine ⟨8260206396241633814097841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11013608528322178418797121 8260206396241633814097841)
            ·
              refine ⟨6195154797181225360573381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8260206396241633814097841 6195154797181225360573381)
              ·
                refine ⟨1161591524471479755107509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6195154797181225360573381 1161591524471479755107509)
                ·
                  refine ⟨108899205419201227041329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1161591524471479755107509 108899205419201227041329)
                  ·
                    rfl

theorem cell21_477181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_477181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_477181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_477181 prefixEnd_477181 := by exact prefixLift 477181
  have htrace : WordTrace (prefixWord ++ tailWord_477181) baseStart_477181 baseEnd_477181 := by
    simpa [prefixWord, tailWord_477181, baseEnd_477181] using wordTrace_append hprefix tailTrace_477181
  have hstable : (prefixWord ++ tailWord_477181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477181).length < 2 ^ (prefixWord ++ tailWord_477181).sum := by decide
  have hdescent : baseEnd_477181 < baseStart_477181 := by decide
  rcases family_descends (prefixWord ++ tailWord_477181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477274 : List Nat := [3, 1, 1, 2, 1, 1, 3, 6, 3]
def baseStart_477274 : Nat := 118140960795 + 477274 * 2 ^ 59
def prefixEnd_477274 : Nat := 4983230072969 + 3 ^ 40 * 477274 * 2
def baseEnd_477274 : Nat := 108920429286253731991139

theorem tailTrace_477274 : CollatzResearch.WordTrace tailWord_477274 prefixEnd_477274 108920429286253731991139 := by
  unfold tailWord_477274
  simp only [CollatzResearch.WordTrace]
  refine ⟨4351903218231321188703719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11605075248616856503209917 4351903218231321188703719)
  ·
    refine ⟨6527854827346981783055579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4351903218231321188703719 6527854827346981783055579)
    ·
      refine ⟨9791782241020472674583369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6527854827346981783055579 9791782241020472674583369)
      ·
        refine ⟨7343836680765354505937527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9791782241020472674583369 7343836680765354505937527)
        ·
          refine ⟨11015755021148031758906291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7343836680765354505937527 11015755021148031758906291)
          ·
            refine ⟨16523632531722047638359437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11015755021148031758906291 16523632531722047638359437)
            ·
              refine ⟨6196362199395767864384789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16523632531722047638359437 6196362199395767864384789)
              ·
                refine ⟨290454478096676618643037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6196362199395767864384789 290454478096676618643037)
                ·
                  refine ⟨108920429286253731991139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 290454478096676618643037 108920429286253731991139)
                  ·
                    rfl

theorem cell21_477274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 6, 3].length) (baseStart_477274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_477274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_477274 prefixEnd_477274 := by exact prefixLift 477274
  have htrace : WordTrace (prefixWord ++ tailWord_477274) baseStart_477274 baseEnd_477274 := by
    simpa [prefixWord, tailWord_477274, baseEnd_477274] using wordTrace_append hprefix tailTrace_477274
  have hstable : (prefixWord ++ tailWord_477274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477274).length < 2 ^ (prefixWord ++ tailWord_477274).sum := by decide
  have hdescent : baseEnd_477274 < baseStart_477274 := by decide
  rcases family_descends (prefixWord ++ tailWord_477274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477392 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 11]
def baseStart_477392 : Nat := 118140960795 + 477392 * 2 ^ 59
def prefixEnd_477392 : Nat := 4983230072969 + 3 ^ 40 * 477392 * 2
def baseEnd_477392 : Nat := 108947358493911749024231

theorem tailTrace_477392 : CollatzResearch.WordTrace tailWord_477392 prefixEnd_477392 108947358493911749024231 := by
  unfold tailWord_477392
  simp only [CollatzResearch.WordTrace]
  refine ⟨8705958343248895453805215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11607944457665193938406953 8705958343248895453805215)
  ·
    refine ⟨13058937514873343180707823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8705958343248895453805215 13058937514873343180707823)
    ·
      refine ⟨19588406272310014771061735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13058937514873343180707823 19588406272310014771061735)
      ·
        refine ⟨29382609408465022156592603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19588406272310014771061735 29382609408465022156592603)
        ·
          refine ⟨44073914112697533234888905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29382609408465022156592603 44073914112697533234888905)
          ·
            refine ⟨33055435584523149926166679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44073914112697533234888905 33055435584523149926166679)
            ·
              refine ⟨49583153376784724889250019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33055435584523149926166679 49583153376784724889250019)
              ·
                refine ⟨74374730065177087333875029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49583153376784724889250019 74374730065177087333875029)
                ·
                  refine ⟨108947358493911749024231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 74374730065177087333875029 108947358493911749024231)
                  ·
                    rfl

theorem cell21_477392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 11].length) (baseStart_477392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_477392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_477392 prefixEnd_477392 := by exact prefixLift 477392
  have htrace : WordTrace (prefixWord ++ tailWord_477392) baseStart_477392 baseEnd_477392 := by
    simpa [prefixWord, tailWord_477392, baseEnd_477392] using wordTrace_append hprefix tailTrace_477392
  have hstable : (prefixWord ++ tailWord_477392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477392).length < 2 ^ (prefixWord ++ tailWord_477392).sum := by decide
  have hdescent : baseEnd_477392 < baseStart_477392 := by decide
  rcases family_descends (prefixWord ++ tailWord_477392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477398 : List Nat := [5, 2, 1, 2, 1, 1, 2, 3, 4]
def baseStart_477398 : Nat := 118140960795 + 477398 * 2 ^ 59
def prefixEnd_477398 : Nat := 4983230072969 + 3 ^ 40 * 477398 * 2
def baseEnd_477398 : Nat := 108948727775657071924219

theorem tailTrace_477398 : CollatzResearch.WordTrace tailWord_477398 prefixEnd_477398 108948727775657071924219 := by
  unfold tailWord_477398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1088258470279753370770553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11608090349650702621552565 1088258470279753370770553)
  ·
    refine ⟨816193852709815028077915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1088258470279753370770553 816193852709815028077915)
    ·
      refine ⟨1224290779064722542116873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 816193852709815028077915 1224290779064722542116873)
      ·
        refine ⟨918218084298541906587655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1224290779064722542116873 918218084298541906587655)
        ·
          refine ⟨1377327126447812859881483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918218084298541906587655 1377327126447812859881483)
          ·
            refine ⟨2065990689671719289822225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1377327126447812859881483 2065990689671719289822225)
            ·
              refine ⟨1549493017253789467366669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2065990689671719289822225 1549493017253789467366669)
              ·
                refine ⟨581059881470171050262501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1549493017253789467366669 581059881470171050262501)
                ·
                  refine ⟨108948727775657071924219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 581059881470171050262501 108948727775657071924219)
                  ·
                    rfl

theorem cell21_477398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_477398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_477398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_477398 prefixEnd_477398 := by exact prefixLift 477398
  have htrace : WordTrace (prefixWord ++ tailWord_477398) baseStart_477398 baseEnd_477398 := by
    simpa [prefixWord, tailWord_477398, baseEnd_477398] using wordTrace_append hprefix tailTrace_477398
  have hstable : (prefixWord ++ tailWord_477398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477398).length < 2 ^ (prefixWord ++ tailWord_477398).sum := by decide
  have hdescent : baseEnd_477398 < baseStart_477398 := by decide
  rcases family_descends (prefixWord ++ tailWord_477398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477409 : List Nat := [1, 2, 3, 1, 3, 1, 3, 2, 5]
def baseStart_477409 : Nat := 118140960795 + 477409 * 2 ^ 59
def prefixEnd_477409 : Nat := 4983230072969 + 3 ^ 40 * 477409 * 2
def baseEnd_477409 : Nat := 108951238125523497240863

theorem tailTrace_477409 : CollatzResearch.WordTrace tailWord_477409 prefixEnd_477409 108951238125523497240863 := by
  unfold tailWord_477409
  simp only [CollatzResearch.WordTrace]
  refine ⟨17412536727436202810979281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11608357818290801873986187 17412536727436202810979281)
  ·
    refine ⟨13059402545577152108234461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17412536727436202810979281 13059402545577152108234461)
    ·
      refine ⟨4897275954591432040587923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13059402545577152108234461 4897275954591432040587923)
      ·
        refine ⟨7345913931887148060881885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4897275954591432040587923 7345913931887148060881885)
        ·
          refine ⟨2754717724457680522830707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7345913931887148060881885 2754717724457680522830707)
          ·
            refine ⟨4132076586686520784246061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2754717724457680522830707 4132076586686520784246061)
            ·
              refine ⟨1549528720007445294092273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4132076586686520784246061 1549528720007445294092273)
              ·
                refine ⟨1162146540005583970569205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1549528720007445294092273 1162146540005583970569205)
                ·
                  refine ⟨108951238125523497240863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1162146540005583970569205 108951238125523497240863)
                  ·
                    rfl

theorem cell21_477409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 5].length) (baseStart_477409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_477409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_477409 prefixEnd_477409 := by exact prefixLift 477409
  have htrace : WordTrace (prefixWord ++ tailWord_477409) baseStart_477409 baseEnd_477409 := by
    simpa [prefixWord, tailWord_477409, baseEnd_477409] using wordTrace_append hprefix tailTrace_477409
  have hstable : (prefixWord ++ tailWord_477409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477409).length < 2 ^ (prefixWord ++ tailWord_477409).sum := by decide
  have hdescent : baseEnd_477409 < baseStart_477409 := by decide
  rcases family_descends (prefixWord ++ tailWord_477409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477440 : List Nat := [2, 1, 1, 2, 1, 1, 7, 2, 4]
def baseStart_477440 : Nat := 118140960795 + 477440 * 2 ^ 59
def prefixEnd_477440 : Nat := 4983230072969 + 3 ^ 40 * 477440 * 2
def baseEnd_477440 : Nat := 108958312747874332224133

theorem tailTrace_477440 : CollatzResearch.WordTrace tailWord_477440 prefixEnd_477440 108958312747874332224133 := by
  unfold tailWord_477440
  simp only [CollatzResearch.WordTrace]
  refine ⟨8706833695161947552678887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11609111593549263403571849 8706833695161947552678887)
  ·
    refine ⟨13060250542742921329018331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8706833695161947552678887 13060250542742921329018331)
    ·
      refine ⟨19590375814114381993527497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13060250542742921329018331 19590375814114381993527497)
      ·
        refine ⟨14692781860585786495145623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19590375814114381993527497 14692781860585786495145623)
        ·
          refine ⟨22039172790878679742718435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14692781860585786495145623 22039172790878679742718435)
          ·
            refine ⟨33058759186318019614077653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22039172790878679742718435 33058759186318019614077653)
            ·
              refine ⟨774814668429328584704945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 33058759186318019614077653 774814668429328584704945)
              ·
                refine ⟨581111001321996438528709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 774814668429328584704945 581111001321996438528709)
                ·
                  refine ⟨108958312747874332224133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 581111001321996438528709 108958312747874332224133)
                  ·
                    rfl

theorem cell21_477440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 4].length) (baseStart_477440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_477440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_477440 prefixEnd_477440 := by exact prefixLift 477440
  have htrace : WordTrace (prefixWord ++ tailWord_477440) baseStart_477440 baseEnd_477440 := by
    simpa [prefixWord, tailWord_477440, baseEnd_477440] using wordTrace_append hprefix tailTrace_477440
  have hstable : (prefixWord ++ tailWord_477440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477440).length < 2 ^ (prefixWord ++ tailWord_477440).sum := by decide
  have hdescent : baseEnd_477440 < baseStart_477440 := by decide
  rcases family_descends (prefixWord ++ tailWord_477440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477454 : List Nat := [4, 1, 1, 2, 1, 2, 2, 8]
def baseStart_477454 : Nat := 118140960795 + 477454 * 2 ^ 59
def prefixEnd_477454 : Nat := 4983230072969 + 3 ^ 40 * 477454 * 2
def baseEnd_477454 : Nat := 36320502579537806330257

theorem tailTrace_477454 : CollatzResearch.WordTrace tailWord_477454 prefixEnd_477454 36320502579537806330257 := by
  unfold tailWord_477454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2176772251534146937045927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11609452008182116997578277 2176772251534146937045927)
  ·
    refine ⟨3265158377301220405568891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2176772251534146937045927 3265158377301220405568891)
    ·
      refine ⟨4897737565951830608353337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3265158377301220405568891 4897737565951830608353337)
      ·
        refine ⟨3673303174463872956265003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4897737565951830608353337 3673303174463872956265003)
        ·
          refine ⟨5509954761695809434397505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3673303174463872956265003 5509954761695809434397505)
          ·
            refine ⟨4132466071271857075798129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5509954761695809434397505 4132466071271857075798129)
            ·
              refine ⟨3099349553453892806848597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4132466071271857075798129 3099349553453892806848597)
              ·
                refine ⟨36320502579537806330257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3099349553453892806848597 36320502579537806330257)
                ·
                  rfl

theorem cell21_477454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_477454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_477454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_477454 prefixEnd_477454 := by exact prefixLift 477454
  have htrace : WordTrace (prefixWord ++ tailWord_477454) baseStart_477454 baseEnd_477454 := by
    simpa [prefixWord, tailWord_477454, baseEnd_477454] using wordTrace_append hprefix tailTrace_477454
  have hstable : (prefixWord ++ tailWord_477454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477454).length < 2 ^ (prefixWord ++ tailWord_477454).sum := by decide
  have hdescent : baseEnd_477454 < baseStart_477454 := by decide
  rcases family_descends (prefixWord ++ tailWord_477454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477457 : List Nat := [1, 2, 2, 1, 1, 6, 3, 1, 4]
def baseStart_477457 : Nat := 118140960795 + 477457 * 2 ^ 59
def prefixEnd_477457 : Nat := 4983230072969 + 3 ^ 40 * 477457 * 2
def baseEnd_477457 : Nat := 108962192379486080440765

theorem tailTrace_477457 : CollatzResearch.WordTrace tailWord_477457 prefixEnd_477457 108962192379486080440765 := by
  unfold tailWord_477457
  simp only [CollatzResearch.WordTrace]
  refine ⟨17414287431262307008726625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11609524954174871339151083 17414287431262307008726625)
  ·
    refine ⟨13060715573446730256544969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17414287431262307008726625 13060715573446730256544969)
    ·
      refine ⟨9795536680085047692408727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13060715573446730256544969 9795536680085047692408727)
      ·
        refine ⟨14693305020127571538613091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9795536680085047692408727 14693305020127571538613091)
        ·
          refine ⟨22039957530191357307919637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14693305020127571538613091 22039957530191357307919637)
          ·
            refine ⟨1033123009227719873808733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22039957530191357307919637 1033123009227719873808733)
            ·
              refine ⟨387421128460394952678275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1033123009227719873808733 387421128460394952678275)
              ·
                refine ⟨581131692690592429017413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387421128460394952678275 581131692690592429017413)
                ·
                  refine ⟨108962192379486080440765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 581131692690592429017413 108962192379486080440765)
                  ·
                    rfl

theorem cell21_477457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 4].length) (baseStart_477457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_477457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_477457 prefixEnd_477457 := by exact prefixLift 477457
  have htrace : WordTrace (prefixWord ++ tailWord_477457) baseStart_477457 baseEnd_477457 := by
    simpa [prefixWord, tailWord_477457, baseEnd_477457] using wordTrace_append hprefix tailTrace_477457
  have hstable : (prefixWord ++ tailWord_477457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477457).length < 2 ^ (prefixWord ++ tailWord_477457).sum := by decide
  have hdescent : baseEnd_477457 < baseStart_477457 := by decide
  rcases family_descends (prefixWord ++ tailWord_477457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477471 : List Nat := [1, 1, 2, 4, 3, 1, 4, 5]
def baseStart_477471 : Nat := 118140960795 + 477471 * 2 ^ 59
def prefixEnd_477471 : Nat := 4983230072969 + 3 ^ 40 * 477471 * 2
def baseEnd_477471 : Nat := 36321795790075055735801

theorem tailTrace_477471 : CollatzResearch.WordTrace tailWord_477471 prefixEnd_477471 36321795790075055735801 := by
  unfold tailWord_477471
  simp only [CollatzResearch.WordTrace]
  refine ⟨17414798053211587399736267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11609865368807724933157511 17414798053211587399736267)
  ·
    refine ⟨26122197079817381099604401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17414798053211587399736267 26122197079817381099604401)
    ·
      refine ⟨19591647809863035824703301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26122197079817381099604401 19591647809863035824703301)
      ·
        refine ⟨3673433964349319217131869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19591647809863035824703301 3673433964349319217131869)
        ·
          refine ⟨1377537736630994706424451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3673433964349319217131869 1377537736630994706424451)
          ·
            refine ⟨2066306604946492059636677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1377537736630994706424451 2066306604946492059636677)
            ·
              refine ⟨387432488427467261181877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2066306604946492059636677 387432488427467261181877)
              ·
                refine ⟨36321795790075055735801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 387432488427467261181877 36321795790075055735801)
                ·
                  rfl

theorem cell21_477471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 5].length) (baseStart_477471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_477471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_477471 prefixEnd_477471 := by exact prefixLift 477471
  have htrace : WordTrace (prefixWord ++ tailWord_477471) baseStart_477471 baseEnd_477471 := by
    simpa [prefixWord, tailWord_477471, baseEnd_477471] using wordTrace_append hprefix tailTrace_477471
  have hstable : (prefixWord ++ tailWord_477471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477471).length < 2 ^ (prefixWord ++ tailWord_477471).sum := by decide
  have hdescent : baseEnd_477471 < baseStart_477471 := by decide
  rcases family_descends (prefixWord ++ tailWord_477471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477502 : List Nat := [4, 2, 1, 2, 1, 2, 3, 1, 5]
def baseStart_477502 : Nat := 118140960795 + 477502 * 2 ^ 59
def prefixEnd_477502 : Nat := 4983230072969 + 3 ^ 40 * 477502 * 2
def baseEnd_477502 : Nat := 108972461992576002190673

theorem tailTrace_477502 : CollatzResearch.WordTrace tailWord_477502 prefixEnd_477502 108972461992576002190673 := by
  unfold tailWord_477502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2176991089512409961764345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11610619144066186462743173 2176991089512409961764345)
  ·
    refine ⟨1632743317134307471323259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2176991089512409961764345 1632743317134307471323259)
    ·
      refine ⟨2449114975701461206984889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1632743317134307471323259 2449114975701461206984889)
      ·
        refine ⟨1836836231776095905238667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2449114975701461206984889 1836836231776095905238667)
        ·
          refine ⟨2755254347664143857858001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1836836231776095905238667 2755254347664143857858001)
          ·
            refine ⟨2066440760748107893393501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2755254347664143857858001 2066440760748107893393501)
            ·
              refine ⟨774915285280540460022563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2066440760748107893393501 774915285280540460022563)
              ·
                refine ⟨1162372927920810690033845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 774915285280540460022563 1162372927920810690033845)
                ·
                  refine ⟨108972461992576002190673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1162372927920810690033845 108972461992576002190673)
                  ·
                    rfl

theorem cell21_477502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_477502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_477502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_477502 prefixEnd_477502 := by exact prefixLift 477502
  have htrace : WordTrace (prefixWord ++ tailWord_477502) baseStart_477502 baseEnd_477502 := by
    simpa [prefixWord, tailWord_477502, baseEnd_477502] using wordTrace_append hprefix tailTrace_477502
  have hstable : (prefixWord ++ tailWord_477502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477502).length < 2 ^ (prefixWord ++ tailWord_477502).sum := by decide
  have hdescent : baseEnd_477502 < baseStart_477502 := by decide
  rcases family_descends (prefixWord ++ tailWord_477502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477508 : List Nat := [2, 3, 4, 1, 3, 1, 2, 1, 4]
def baseStart_477508 : Nat := 118140960795 + 477508 * 2 ^ 59
def prefixEnd_477508 : Nat := 4983230072969 + 3 ^ 40 * 477508 * 2
def baseEnd_477508 : Nat := 108973831274321325090661

theorem tailTrace_477508 : CollatzResearch.WordTrace tailWord_477508 prefixEnd_477508 108973831274321325090661 := by
  unfold tailWord_477508
  simp only [CollatzResearch.WordTrace]
  refine ⟨8708073777038771359416589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11610765036051695145888785 8708073777038771359416589)
  ·
    refine ⟨3265527666389539259781221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8708073777038771359416589 3265527666389539259781221)
    ·
      refine ⟨612286437448038611208979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3265527666389539259781221 612286437448038611208979)
      ·
        refine ⟨918429656172057916813469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612286437448038611208979 918429656172057916813469)
        ·
          refine ⟨344411121064521718805051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 918429656172057916813469 344411121064521718805051)
          ·
            refine ⟨516616681596782578207577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344411121064521718805051 516616681596782578207577)
            ·
              refine ⟨387462511197586933655683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 516616681596782578207577 387462511197586933655683)
              ·
                refine ⟨581193766796380400483525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387462511197586933655683 581193766796380400483525)
                ·
                  refine ⟨108973831274321325090661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 581193766796380400483525 108973831274321325090661)
                  ·
                    rfl

theorem cell21_477508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_477508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_477508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_477508 prefixEnd_477508 := by exact prefixLift 477508
  have htrace : WordTrace (prefixWord ++ tailWord_477508) baseStart_477508 baseEnd_477508 := by
    simpa [prefixWord, tailWord_477508, baseEnd_477508] using wordTrace_append hprefix tailTrace_477508
  have hstable : (prefixWord ++ tailWord_477508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477508).length < 2 ^ (prefixWord ++ tailWord_477508).sum := by decide
  have hdescent : baseEnd_477508 < baseStart_477508 := by decide
  rcases family_descends (prefixWord ++ tailWord_477508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477516 : List Nat := [2, 2, 1, 3, 2, 1, 3, 3, 4]
def baseStart_477516 : Nat := 118140960795 + 477516 * 2 ^ 59
def prefixEnd_477516 : Nat := 4983230072969 + 3 ^ 40 * 477516 * 2
def baseEnd_477516 : Nat := 108975656983315088957311

theorem tailTrace_477516 : CollatzResearch.WordTrace tailWord_477516 prefixEnd_477516 108975656983315088957311 := by
  unfold tailWord_477516
  simp only [CollatzResearch.WordTrace]
  refine ⟨8708219669024280042562201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11610959558699040056749601 8708219669024280042562201)
  ·
    refine ⟨6531164751768210031921651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8708219669024280042562201 6531164751768210031921651)
    ·
      refine ⟨9796747127652315047882477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6531164751768210031921651 9796747127652315047882477)
      ·
        refine ⟨3673780172869618142955929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9796747127652315047882477 3673780172869618142955929)
        ·
          refine ⟨2755335129652213607216947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3673780172869618142955929 2755335129652213607216947)
          ·
            refine ⟨4133002694478320410825421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2755335129652213607216947 4133002694478320410825421)
            ·
              refine ⟨1549876010429370154059533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4133002694478320410825421 1549876010429370154059533)
              ·
                refine ⟨581203503911013807772325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1549876010429370154059533 581203503911013807772325)
                ·
                  refine ⟨108975656983315088957311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 581203503911013807772325 108975656983315088957311)
                  ·
                    rfl

theorem cell21_477516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_477516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_477516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_477516 prefixEnd_477516 := by exact prefixLift 477516
  have htrace : WordTrace (prefixWord ++ tailWord_477516) baseStart_477516 baseEnd_477516 := by
    simpa [prefixWord, tailWord_477516, baseEnd_477516] using wordTrace_append hprefix tailTrace_477516
  have hstable : (prefixWord ++ tailWord_477516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477516).length < 2 ^ (prefixWord ++ tailWord_477516).sum := by decide
  have hdescent : baseEnd_477516 < baseStart_477516 := by decide
  rcases family_descends (prefixWord ++ tailWord_477516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477671 : List Nat := [1, 1, 5, 2, 1, 1, 5, 2, 3]
def baseStart_477671 : Nat := 118140960795 + 477671 * 2 ^ 59
def prefixEnd_477671 : Nat := 4983230072969 + 3 ^ 40 * 477671 * 2
def baseEnd_477671 : Nat := 109011030095069263873661

theorem tailTrace_477671 : CollatzResearch.WordTrace tailWord_477671 prefixEnd_477671 109011030095069263873661 := by
  unfold tailWord_477671
  simp only [CollatzResearch.WordTrace]
  refine ⟨17422092652487021557016867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11614728434991347704677911 17422092652487021557016867)
  ·
    refine ⟨26133138978730532335525301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17422092652487021557016867 26133138978730532335525301)
    ·
      refine ⟨2449981779255987406455497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26133138978730532335525301 2449981779255987406455497)
      ·
        refine ⟨1837486334441990554841623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2449981779255987406455497 1837486334441990554841623)
        ·
          refine ⟨2756229501662985832262435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1837486334441990554841623 2756229501662985832262435)
          ·
            refine ⟨4134344252494478748393653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2756229501662985832262435 4134344252494478748393653)
            ·
              refine ⟨387594773671357382661905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4134344252494478748393653 387594773671357382661905)
              ·
                refine ⟨290696080253518036996429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 387594773671357382661905 290696080253518036996429)
                ·
                  refine ⟨109011030095069263873661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 290696080253518036996429 109011030095069263873661)
                  ·
                    rfl

theorem cell21_477671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 2, 3].length) (baseStart_477671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_477671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_477671 prefixEnd_477671 := by exact prefixLift 477671
  have htrace : WordTrace (prefixWord ++ tailWord_477671) baseStart_477671 baseEnd_477671 := by
    simpa [prefixWord, tailWord_477671, baseEnd_477671] using wordTrace_append hprefix tailTrace_477671
  have hstable : (prefixWord ++ tailWord_477671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477671).length < 2 ^ (prefixWord ++ tailWord_477671).sum := by decide
  have hdescent : baseEnd_477671 < baseStart_477671 := by decide
  rcases family_descends (prefixWord ++ tailWord_477671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477772 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 7]
def baseStart_477772 : Nat := 118140960795 + 477772 * 2 ^ 59
def prefixEnd_477772 : Nat := 4983230072969 + 3 ^ 40 * 477772 * 2
def baseEnd_477772 : Nat := 109034079671115532690121

theorem tailTrace_477772 : CollatzResearch.WordTrace tailWord_477772 prefixEnd_477772 109034079671115532690121 := by
  unfold tailWord_477772
  simp only [CollatzResearch.WordTrace]
  refine ⟨8712888212560557903221785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11617184283414077204295713 8712888212560557903221785)
  ·
    refine ⟨6534666159420418427416339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8712888212560557903221785 6534666159420418427416339)
    ·
      refine ⟨9801999239130627641124509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6534666159420418427416339 9801999239130627641124509)
      ·
        refine ⟨3675749714673985365421691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9801999239130627641124509 3675749714673985365421691)
        ·
          refine ⟨5513624572010978048132537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3675749714673985365421691 5513624572010978048132537)
          ·
            refine ⟨4135218429008233536099403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5513624572010978048132537 4135218429008233536099403)
            ·
              refine ⟨6202827643512350304149105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4135218429008233536099403 6202827643512350304149105)
              ·
                refine ⟨4652120732634262728111829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6202827643512350304149105 4652120732634262728111829)
                ·
                  refine ⟨109034079671115532690121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4652120732634262728111829 109034079671115532690121)
                  ·
                    rfl

theorem cell21_477772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_477772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_477772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_477772 prefixEnd_477772 := by exact prefixLift 477772
  have htrace : WordTrace (prefixWord ++ tailWord_477772) baseStart_477772 baseEnd_477772 := by
    simpa [prefixWord, tailWord_477772, baseEnd_477772] using wordTrace_append hprefix tailTrace_477772
  have hstable : (prefixWord ++ tailWord_477772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477772).length < 2 ^ (prefixWord ++ tailWord_477772).sum := by decide
  have hdescent : baseEnd_477772 < baseStart_477772 := by decide
  rcases family_descends (prefixWord ++ tailWord_477772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477826 : List Nat := [3, 4, 3, 1, 2, 1, 7]
def baseStart_477826 : Nat := 118140960795 + 477826 * 2 ^ 59
def prefixEnd_477826 : Nat := 4983230072969 + 3 ^ 40 * 477826 * 2
def baseEnd_477826 : Nat := 12116267022980382087779

theorem tailTrace_477826 : CollatzResearch.WordTrace tailWord_477826 prefixEnd_477826 12116267022980382087779 := by
  unfold tailWord_477826
  simp only [CollatzResearch.WordTrace]
  refine ⟨4356936491731370757227333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11618497311283655352606221 4356936491731370757227333)
  ·
    refine ⟨816925592199632016980125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4356936491731370757227333 816925592199632016980125)
    ·
      refine ⟨306347097074862006367547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 816925592199632016980125 306347097074862006367547)
      ·
        refine ⟨459520645612293009551321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306347097074862006367547 459520645612293009551321)
        ·
          refine ⟨344640484209219757163491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459520645612293009551321 344640484209219757163491)
          ·
            refine ⟨516960726313829635745237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344640484209219757163491 516960726313829635745237)
            ·
              refine ⟨12116267022980382087779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 516960726313829635745237 12116267022980382087779)
              ·
                rfl

theorem cell21_477826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 7].length) (baseStart_477826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_477826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_477826 prefixEnd_477826 := by exact prefixLift 477826
  have htrace : WordTrace (prefixWord ++ tailWord_477826) baseStart_477826 baseEnd_477826 := by
    simpa [prefixWord, tailWord_477826, baseEnd_477826] using wordTrace_append hprefix tailTrace_477826
  have hstable : (prefixWord ++ tailWord_477826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477826).length < 2 ^ (prefixWord ++ tailWord_477826).sum := by decide
  have hdescent : baseEnd_477826 < baseStart_477826 := by decide
  rcases family_descends (prefixWord ++ tailWord_477826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477896 : List Nat := [2, 1, 3, 1, 2, 4, 2, 2, 4]
def baseStart_477896 : Nat := 118140960795 + 477896 * 2 ^ 59
def prefixEnd_477896 : Nat := 4983230072969 + 3 ^ 40 * 477896 * 2
def baseEnd_477896 : Nat := 109062378160518872623201

theorem tailTrace_477896 : CollatzResearch.WordTrace tailWord_477896 prefixEnd_477896 109062378160518872623201 := by
  unfold tailWord_477896
  simp only [CollatzResearch.WordTrace]
  refine ⟨8715149538335942491978771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11620199384447923322638361 8715149538335942491978771)
  ·
    refine ⟨13072724307503913737968157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8715149538335942491978771 13072724307503913737968157)
    ·
      refine ⟨4902271615313967651738059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13072724307503913737968157 4902271615313967651738059)
      ·
        refine ⟨7353407422970951477607089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4902271615313967651738059 7353407422970951477607089)
        ·
          refine ⟨5515055567228213608205317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7353407422970951477607089 5515055567228213608205317)
          ·
            refine ⟨1034072918855290051538497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5515055567228213608205317 1034072918855290051538497)
            ·
              refine ⟨775554689141467538653873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1034072918855290051538497 775554689141467538653873)
              ·
                refine ⟨581666016856100653990405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 775554689141467538653873 581666016856100653990405)
                ·
                  refine ⟨109062378160518872623201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 581666016856100653990405 109062378160518872623201)
                  ·
                    rfl

theorem cell21_477896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 4].length) (baseStart_477896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_477896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_477896 prefixEnd_477896 := by exact prefixLift 477896
  have htrace : WordTrace (prefixWord ++ tailWord_477896) baseStart_477896 baseEnd_477896 := by
    simpa [prefixWord, tailWord_477896, baseEnd_477896] using wordTrace_append hprefix tailTrace_477896
  have hstable : (prefixWord ++ tailWord_477896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477896).length < 2 ^ (prefixWord ++ tailWord_477896).sum := by decide
  have hdescent : baseEnd_477896 < baseStart_477896 := by decide
  rcases family_descends (prefixWord ++ tailWord_477896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477924 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 7]
def baseStart_477924 : Nat := 118140960795 + 477924 * 2 ^ 59
def prefixEnd_477924 : Nat := 4983230072969 + 3 ^ 40 * 477924 * 2
def baseEnd_477924 : Nat := 109068768141997046156477

theorem tailTrace_477924 : CollatzResearch.WordTrace tailWord_477924 prefixEnd_477924 109068768141997046156477 := by
  unfold tailWord_477924
  simp only [CollatzResearch.WordTrace]
  refine ⟨8715660160285222882988413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11620880213713630510651217 8715660160285222882988413)
  ·
    refine ⟨3268372560106958581120655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8715660160285222882988413 3268372560106958581120655)
    ·
      refine ⟨4902558840160437871680983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3268372560106958581120655 4902558840160437871680983)
      ·
        refine ⟨7353838260240656807521475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4902558840160437871680983 7353838260240656807521475)
        ·
          refine ⟨11030757390360985211282213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7353838260240656807521475 11030757390360985211282213)
          ·
            refine ⟨2068267010692684727115415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11030757390360985211282213 2068267010692684727115415)
            ·
              refine ⟨3102400516039027090673123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2068267010692684727115415 3102400516039027090673123)
              ·
                refine ⟨4653600774058540636009685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3102400516039027090673123 4653600774058540636009685)
                ·
                  refine ⟨109068768141997046156477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4653600774058540636009685 109068768141997046156477)
                  ·
                    rfl

theorem cell21_477924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_477924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_477924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_477924 prefixEnd_477924 := by exact prefixLift 477924
  have htrace : WordTrace (prefixWord ++ tailWord_477924) baseStart_477924 baseEnd_477924 := by
    simpa [prefixWord, tailWord_477924, baseEnd_477924] using wordTrace_append hprefix tailTrace_477924
  have hstable : (prefixWord ++ tailWord_477924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477924).length < 2 ^ (prefixWord ++ tailWord_477924).sum := by decide
  have hdescent : baseEnd_477924 < baseStart_477924 := by decide
  rcases family_descends (prefixWord ++ tailWord_477924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477986 : List Nat := [3, 3, 1, 1, 2, 3, 1, 7]
def baseStart_477986 : Nat := 118140960795 + 477986 * 2 ^ 59
def prefixEnd_477986 : Nat := 4983230072969 + 3 ^ 40 * 477986 * 2
def baseEnd_477986 : Nat := 36360972462232905374339

theorem tailTrace_477986 : CollatzResearch.WordTrace tailWord_477986 prefixEnd_477986 36360972462232905374339 := by
  unfold tailWord_477986
  simp only [CollatzResearch.WordTrace]
  refine ⟨4358395411586457588683453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11622387764230553569822541 4358395411586457588683453)
  ·
    refine ⟨1634398279344921595756295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4358395411586457588683453 1634398279344921595756295)
    ·
      refine ⟨2451597419017382393634443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1634398279344921595756295 2451597419017382393634443)
      ·
        refine ⟨3677396128526073590451665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2451597419017382393634443 3677396128526073590451665)
        ·
          refine ⟨2758047096394555192838749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3677396128526073590451665 2758047096394555192838749)
          ·
            refine ⟨1034267661147958197314531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2758047096394555192838749 1034267661147958197314531)
            ·
              refine ⟨1551401491721937295971797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1034267661147958197314531 1551401491721937295971797)
              ·
                refine ⟨36360972462232905374339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1551401491721937295971797 36360972462232905374339)
                ·
                  rfl

theorem cell21_477986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 7].length) (baseStart_477986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_477986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_477986 prefixEnd_477986 := by exact prefixLift 477986
  have htrace : WordTrace (prefixWord ++ tailWord_477986) baseStart_477986 baseEnd_477986 := by
    simpa [prefixWord, tailWord_477986, baseEnd_477986] using wordTrace_append hprefix tailTrace_477986
  have hstable : (prefixWord ++ tailWord_477986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477986).length < 2 ^ (prefixWord ++ tailWord_477986).sum := by decide
  have hdescent : baseEnd_477986 < baseStart_477986 := by decide
  rcases family_descends (prefixWord ++ tailWord_477986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478020 : List Nat := [2, 3, 4, 2, 1, 1, 2, 6]
def baseStart_478020 : Nat := 118140960795 + 478020 * 2 ^ 59
def prefixEnd_478020 : Nat := 4983230072969 + 3 ^ 40 * 478020 * 2
def baseEnd_478020 : Nat := 36363558883307404185427

theorem tailTrace_478020 : CollatzResearch.WordTrace tailWord_478020 prefixEnd_478020 36363558883307404185427 := by
  unfold tailWord_478020
  simp only [CollatzResearch.WordTrace]
  refine ⟨8717410864111327080735757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11623214485481769440981009 8717410864111327080735757)
  ·
    refine ⟨3269029074041747655275909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8717410864111327080735757 3269029074041747655275909)
    ·
      refine ⟨612942951382827685364233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3269029074041747655275909 612942951382827685364233)
      ·
        refine ⟨459707213537120764023175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 612942951382827685364233 459707213537120764023175)
        ·
          refine ⟨689560820305681146034763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459707213537120764023175 689560820305681146034763)
          ·
            refine ⟨1034341230458521719052145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689560820305681146034763 1034341230458521719052145)
            ·
              refine ⟨775755922843891289289109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1034341230458521719052145 775755922843891289289109)
              ·
                refine ⟨36363558883307404185427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 775755922843891289289109 36363558883307404185427)
                ·
                  rfl

theorem cell21_478020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 6].length) (baseStart_478020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_478020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_478020 prefixEnd_478020 := by exact prefixLift 478020
  have htrace : WordTrace (prefixWord ++ tailWord_478020) baseStart_478020 baseEnd_478020 := by
    simpa [prefixWord, tailWord_478020, baseEnd_478020] using wordTrace_append hprefix tailTrace_478020
  have hstable : (prefixWord ++ tailWord_478020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478020).length < 2 ^ (prefixWord ++ tailWord_478020).sum := by decide
  have hdescent : baseEnd_478020 < baseStart_478020 := by decide
  rcases family_descends (prefixWord ++ tailWord_478020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478062 : List Nat := [4, 1, 2, 3, 2, 9]
def baseStart_478062 : Nat := 118140960795 + 478062 * 2 ^ 59
def prefixEnd_478062 : Nat := 4983230072969 + 3 ^ 40 * 478062 * 2
def baseEnd_478062 : Nat := 4040750430449610105785

theorem tailTrace_478062 : CollatzResearch.WordTrace tailWord_478062 prefixEnd_478062 4040750430449610105785 := by
  unfold tailWord_478062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2179544199258811916812555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11624235729380330223000293 2179544199258811916812555)
  ·
    refine ⟨3269316298888217875218833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2179544199258811916812555 3269316298888217875218833)
    ·
      refine ⟨2451987224166163406414125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3269316298888217875218833 2451987224166163406414125)
      ·
        refine ⟨919495209062311277405297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2451987224166163406414125 919495209062311277405297)
        ·
          refine ⟨689621406796733458053973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 919495209062311277405297 689621406796733458053973)
          ·
            refine ⟨4040750430449610105785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 689621406796733458053973 4040750430449610105785)
            ·
              rfl

theorem cell21_478062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 9].length) (baseStart_478062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_478062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_478062 prefixEnd_478062 := by exact prefixLift 478062
  have htrace : WordTrace (prefixWord ++ tailWord_478062) baseStart_478062 baseEnd_478062 := by
    simpa [prefixWord, tailWord_478062, baseEnd_478062] using wordTrace_append hprefix tailTrace_478062
  have hstable : (prefixWord ++ tailWord_478062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478062).length < 2 ^ (prefixWord ++ tailWord_478062).sum := by decide
  have hdescent : baseEnd_478062 < baseStart_478062 := by decide
  rcases family_descends (prefixWord ++ tailWord_478062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478141 : List Nat := [1, 4, 1, 2, 4, 1, 3, 1, 4]
def baseStart_478141 : Nat := 118140960795 + 478141 * 2 ^ 59
def prefixEnd_478141 : Nat := 4983230072969 + 3 ^ 40 * 478141 * 2
def baseEnd_478141 : Nat := 109118290498452891039367

theorem tailTrace_478141 : CollatzResearch.WordTrace tailWord_478141 prefixEnd_478141 109118290498452891039367 := by
  unfold tailWord_478141
  simp only [CollatzResearch.WordTrace]
  refine ⟨17439234960784291826626277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11626156640522861217750851 17439234960784291826626277)
  ·
    refine ⟨3269856555147054717492427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17439234960784291826626277 3269856555147054717492427)
    ·
      refine ⟨4904784832720582076238641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3269856555147054717492427 4904784832720582076238641)
      ·
        refine ⟨3678588624540436557178981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4904784832720582076238641 3678588624540436557178981)
        ·
          refine ⟨689735367101331854471059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3678588624540436557178981 689735367101331854471059)
          ·
            refine ⟨1034603050651997781706589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689735367101331854471059 1034603050651997781706589)
            ·
              refine ⟨387976143994499168139971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1034603050651997781706589 387976143994499168139971)
              ·
                refine ⟨581964215991748752209957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387976143994499168139971 581964215991748752209957)
                ·
                  refine ⟨109118290498452891039367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 581964215991748752209957 109118290498452891039367)
                  ·
                    rfl

theorem cell21_478141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_478141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_478141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_478141 prefixEnd_478141 := by exact prefixLift 478141
  have htrace : WordTrace (prefixWord ++ tailWord_478141) baseStart_478141 baseEnd_478141 := by
    simpa [prefixWord, tailWord_478141, baseEnd_478141] using wordTrace_append hprefix tailTrace_478141
  have hstable : (prefixWord ++ tailWord_478141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478141).length < 2 ^ (prefixWord ++ tailWord_478141).sum := by decide
  have hdescent : baseEnd_478141 < baseStart_478141 := by decide
  rcases family_descends (prefixWord ++ tailWord_478141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478183 : List Nat := [1, 1, 5, 2, 2, 1, 2, 1, 6]
def baseStart_478183 : Nat := 118140960795 + 478183 * 2 ^ 59
def prefixEnd_478183 : Nat := 4983230072969 + 3 ^ 40 * 478183 * 2
def baseEnd_478183 : Nat := 109127875470670151339281

theorem tailTrace_478183 : CollatzResearch.WordTrace tailWord_478183 prefixEnd_478183 109127875470670151339281 := by
  unfold tailWord_478183
  simp only [CollatzResearch.WordTrace]
  refine ⟨17440766826632132999655203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11627177884421421999770135 17440766826632132999655203)
  ·
    refine ⟨26161150239948199499482805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17440766826632132999655203 26161150239948199499482805)
    ·
      refine ⟨2452607834995143703076513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26161150239948199499482805 2452607834995143703076513)
      ·
        refine ⟨1839455876246357777307385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2452607834995143703076513 1839455876246357777307385)
        ·
          refine ⟨1379591907184768332980539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1839455876246357777307385 1379591907184768332980539)
          ·
            refine ⟨2069387860777152499470809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1379591907184768332980539 2069387860777152499470809)
            ·
              refine ⟨1552040895582864374603107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2069387860777152499470809 1552040895582864374603107)
              ·
                refine ⟨2328061343374296561904661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1552040895582864374603107 2328061343374296561904661)
                ·
                  refine ⟨109127875470670151339281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2328061343374296561904661 109127875470670151339281)
                  ·
                    rfl

theorem cell21_478183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 6].length) (baseStart_478183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_478183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_478183 prefixEnd_478183 := by exact prefixLift 478183
  have htrace : WordTrace (prefixWord ++ tailWord_478183) baseStart_478183 baseEnd_478183 := by
    simpa [prefixWord, tailWord_478183, baseEnd_478183] using wordTrace_append hprefix tailTrace_478183
  have hstable : (prefixWord ++ tailWord_478183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478183).length < 2 ^ (prefixWord ++ tailWord_478183).sum := by decide
  have hdescent : baseEnd_478183 < baseStart_478183 := by decide
  rcases family_descends (prefixWord ++ tailWord_478183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478245 : List Nat := [1, 3, 1, 2, 2, 2, 3, 4, 3]
def baseStart_478245 : Nat := 118140960795 + 478245 * 2 ^ 59
def prefixEnd_478245 : Nat := 4983230072969 + 3 ^ 40 * 478245 * 2
def baseEnd_478245 : Nat := 109142024715371821305821

theorem tailTrace_478245 : CollatzResearch.WordTrace tailWord_478245 prefixEnd_478245 109142024715371821305821 := by
  unfold tailWord_478245
  simp only [CollatzResearch.WordTrace]
  refine ⟨17443028152407517588412189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11628685434938345058941459 17443028152407517588412189)
  ·
    refine ⟨6541135557152819095654571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17443028152407517588412189 6541135557152819095654571)
    ·
      refine ⟨9811703335729228643481857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6541135557152819095654571 9811703335729228643481857)
      ·
        refine ⟨7358777501796921482611393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9811703335729228643481857 7358777501796921482611393)
        ·
          refine ⟨5519083126347691111958545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7358777501796921482611393 5519083126347691111958545)
          ·
            refine ⟨4139312344760768333968909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5519083126347691111958545 4139312344760768333968909)
            ·
              refine ⟨1552242129285288125238341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4139312344760768333968909 1552242129285288125238341)
              ·
                refine ⟨291045399240991523482189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1552242129285288125238341 291045399240991523482189)
                ·
                  refine ⟨109142024715371821305821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 291045399240991523482189 109142024715371821305821)
                  ·
                    rfl

theorem cell21_478245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 4, 3].length) (baseStart_478245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_478245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_478245 prefixEnd_478245 := by exact prefixLift 478245
  have htrace : WordTrace (prefixWord ++ tailWord_478245) baseStart_478245 baseEnd_478245 := by
    simpa [prefixWord, tailWord_478245, baseEnd_478245] using wordTrace_append hprefix tailTrace_478245
  have hstable : (prefixWord ++ tailWord_478245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478245).length < 2 ^ (prefixWord ++ tailWord_478245).sum := by decide
  have hdescent : baseEnd_478245 < baseStart_478245 := by decide
  rcases family_descends (prefixWord ++ tailWord_478245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478304 : List Nat := [2, 1, 1, 3, 2, 2, 4, 1, 5]
def baseStart_478304 : Nat := 118140960795 + 478304 * 2 ^ 59
def prefixEnd_478304 : Nat := 4983230072969 + 3 ^ 40 * 478304 * 2
def baseEnd_478304 : Nat := 109155489319200829822367

theorem tailTrace_478304 : CollatzResearch.WordTrace tailWord_478304 prefixEnd_478304 109155489319200829822367 := by
  unfold tailWord_478304
  simp only [CollatzResearch.WordTrace]
  refine ⟨8722590029596885332404983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11630120039462513776539977 8722590029596885332404983)
  ·
    refine ⟨13083885044395327998607475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8722590029596885332404983 13083885044395327998607475)
    ·
      refine ⟨19625827566592991997911213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13083885044395327998607475 19625827566592991997911213)
      ·
        refine ⟨7359685337472371999216705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19625827566592991997911213 7359685337472371999216705)
        ·
          refine ⟨5519764003104278999412529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7359685337472371999216705 5519764003104278999412529)
          ·
            refine ⟨4139823002328209249559397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5519764003104278999412529 4139823002328209249559397)
            ·
              refine ⟨776216812936539234292387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4139823002328209249559397 776216812936539234292387)
              ·
                refine ⟨1164325219404808851438581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776216812936539234292387 1164325219404808851438581)
                ·
                  refine ⟨109155489319200829822367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1164325219404808851438581 109155489319200829822367)
                  ·
                    rfl

theorem cell21_478304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 5].length) (baseStart_478304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_478304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_478304 prefixEnd_478304 := by exact prefixLift 478304
  have htrace : WordTrace (prefixWord ++ tailWord_478304) baseStart_478304 baseEnd_478304 := by
    simpa [prefixWord, tailWord_478304, baseEnd_478304] using wordTrace_append hprefix tailTrace_478304
  have hstable : (prefixWord ++ tailWord_478304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478304).length < 2 ^ (prefixWord ++ tailWord_478304).sum := by decide
  have hdescent : baseEnd_478304 < baseStart_478304 := by decide
  rcases family_descends (prefixWord ++ tailWord_478304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478366 : List Nat := [4, 3, 1, 1, 2, 1, 1, 8]
def baseStart_478366 : Nat := 118140960795 + 478366 * 2 ^ 59
def prefixEnd_478366 : Nat := 4983230072969 + 3 ^ 40 * 478366 * 2
def baseEnd_478366 : Nat := 36389879521300833262969

theorem tailTrace_478366 : CollatzResearch.WordTrace tailWord_478366 prefixEnd_478366 36389879521300833262969 := by
  unfold tailWord_478366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2180930173121144406695869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11631627589979436835711301 2180930173121144406695869)
  ·
    refine ⟨817848814920429152510951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2180930173121144406695869 817848814920429152510951)
    ·
      refine ⟨1226773222380643728766427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 817848814920429152510951 1226773222380643728766427)
      ·
        refine ⟨1840159833570965593149641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1226773222380643728766427 1840159833570965593149641)
        ·
          refine ⟨1380119875178224194862231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1840159833570965593149641 1380119875178224194862231)
          ·
            refine ⟨2070179812767336292293347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1380119875178224194862231 2070179812767336292293347)
            ·
              refine ⟨3105269719151004438440021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2070179812767336292293347 3105269719151004438440021)
              ·
                refine ⟨36389879521300833262969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3105269719151004438440021 36389879521300833262969)
                ·
                  rfl

theorem cell21_478366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_478366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_478366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_478366 prefixEnd_478366 := by exact prefixLift 478366
  have htrace : WordTrace (prefixWord ++ tailWord_478366) baseStart_478366 baseEnd_478366 := by
    simpa [prefixWord, tailWord_478366, baseEnd_478366] using wordTrace_append hprefix tailTrace_478366
  have hstable : (prefixWord ++ tailWord_478366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478366).length < 2 ^ (prefixWord ++ tailWord_478366).sum := by decide
  have hdescent : baseEnd_478366 < baseStart_478366 := by decide
  rcases family_descends (prefixWord ++ tailWord_478366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478406 : List Nat := [6, 1, 2, 2, 1, 2, 2, 2, 3]
def baseStart_478406 : Nat := 118140960795 + 478406 * 2 ^ 59
def prefixEnd_478406 : Nat := 4983230072969 + 3 ^ 40 * 478406 * 2
def baseEnd_478406 : Nat := 109178767108871319122159

theorem tailTrace_478406 : CollatzResearch.WordTrace tailWord_478406 prefixEnd_478406 109178767108871319122159 := by
  unfold tailWord_478406
  simp only [CollatzResearch.WordTrace]
  refine ⟨545278134525757565156971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11632600203216161390015381 545278134525757565156971)
  ·
    refine ⟨817917201788636347735457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 545278134525757565156971 817917201788636347735457)
    ·
      refine ⟨613437901341477260801593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 817917201788636347735457 613437901341477260801593)
      ·
        refine ⟨460078426006107945601195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613437901341477260801593 460078426006107945601195)
        ·
          refine ⟨690117639009161918401793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460078426006107945601195 690117639009161918401793)
          ·
            refine ⟨517588229256871438801345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 690117639009161918401793 517588229256871438801345)
            ·
              refine ⟨388191171942653579101009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 517588229256871438801345 388191171942653579101009)
              ·
                refine ⟨291143378956990184325757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 388191171942653579101009 291143378956990184325757)
                ·
                  refine ⟨109178767108871319122159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 291143378956990184325757 109178767108871319122159)
                  ·
                    rfl

theorem cell21_478406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_478406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_478406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_478406 prefixEnd_478406 := by exact prefixLift 478406
  have htrace : WordTrace (prefixWord ++ tailWord_478406) baseStart_478406 baseEnd_478406 := by
    simpa [prefixWord, tailWord_478406, baseEnd_478406] using wordTrace_append hprefix tailTrace_478406
  have hstable : (prefixWord ++ tailWord_478406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478406).length < 2 ^ (prefixWord ++ tailWord_478406).sum := by decide
  have hdescent : baseEnd_478406 < baseStart_478406 := by decide
  rcases family_descends (prefixWord ++ tailWord_478406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478414 : List Nat := [4, 1, 1, 1, 5, 1, 1, 4, 3]
def baseStart_478414 : Nat := 118140960795 + 478414 * 2 ^ 59
def prefixEnd_478414 : Nat := 4983230072969 + 3 ^ 40 * 478414 * 2
def baseEnd_478414 : Nat := 109180592817865082988809

theorem tailTrace_478414 : CollatzResearch.WordTrace tailWord_478414 prefixEnd_478414 109180592817865082988809 := by
  unfold tailWord_478414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2181149011099407431414287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11632794725863506300876197 2181149011099407431414287)
  ·
    refine ⟨3271723516649111147121431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2181149011099407431414287 3271723516649111147121431)
    ·
      refine ⟨4907585274973666720682147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3271723516649111147121431 4907585274973666720682147)
      ·
        refine ⟨7361377912460500081023221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4907585274973666720682147 7361377912460500081023221)
        ·
          refine ⟨690129179293171882595927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7361377912460500081023221 690129179293171882595927)
          ·
            refine ⟨1035193768939757823893891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690129179293171882595927 1035193768939757823893891)
            ·
              refine ⟨1552790653409636735840837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035193768939757823893891 1552790653409636735840837)
              ·
                refine ⟨291148247514306887970157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1552790653409636735840837 291148247514306887970157)
                ·
                  refine ⟨109180592817865082988809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 291148247514306887970157 109180592817865082988809)
                  ·
                    rfl

theorem cell21_478414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_478414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_478414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_478414 prefixEnd_478414 := by exact prefixLift 478414
  have htrace : WordTrace (prefixWord ++ tailWord_478414) baseStart_478414 baseEnd_478414 := by
    simpa [prefixWord, tailWord_478414, baseEnd_478414] using wordTrace_append hprefix tailTrace_478414
  have hstable : (prefixWord ++ tailWord_478414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478414).length < 2 ^ (prefixWord ++ tailWord_478414).sum := by decide
  have hdescent : baseEnd_478414 < baseStart_478414 := by decide
  rcases family_descends (prefixWord ++ tailWord_478414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478442 : List Nat := [3, 1, 3, 1, 1, 4, 3, 5]
def baseStart_478442 : Nat := 118140960795 + 478442 * 2 ^ 59
def prefixEnd_478442 : Nat := 4983230072969 + 3 ^ 40 * 478442 * 2
def baseEnd_478442 : Nat := 36395660933114418840695

theorem tailTrace_478442 : CollatzResearch.WordTrace tailWord_478442 prefixEnd_478442 36395660933114418840695 := by
  unfold tailWord_478442
  simp only [CollatzResearch.WordTrace]
  refine ⟨4362553333173455058333395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11633475555129213488889053 4362553333173455058333395)
  ·
    refine ⟨6543829999760182587500093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4362553333173455058333395 6543829999760182587500093)
    ·
      refine ⟨2453936249910068470312535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6543829999760182587500093 2453936249910068470312535)
      ·
        refine ⟨3680904374865102705468803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2453936249910068470312535 3680904374865102705468803)
        ·
          refine ⟨5521356562297654058203205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3680904374865102705468803 5521356562297654058203205)
          ·
            refine ⟨1035254355430810135913101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5521356562297654058203205 1035254355430810135913101)
            ·
              refine ⟨388220383286553800967413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1035254355430810135913101 388220383286553800967413)
              ·
                refine ⟨36395660933114418840695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 388220383286553800967413 36395660933114418840695)
                ·
                  rfl

theorem cell21_478442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 5].length) (baseStart_478442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_478442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_478442 prefixEnd_478442 := by exact prefixLift 478442
  have htrace : WordTrace (prefixWord ++ tailWord_478442) baseStart_478442 baseEnd_478442 := by
    simpa [prefixWord, tailWord_478442, baseEnd_478442] using wordTrace_append hprefix tailTrace_478442
  have hstable : (prefixWord ++ tailWord_478442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478442).length < 2 ^ (prefixWord ++ tailWord_478442).sum := by decide
  have hdescent : baseEnd_478442 < baseStart_478442 := by decide
  rcases family_descends (prefixWord ++ tailWord_478442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478501 : List Nat := [1, 3, 1, 2, 4, 2, 1, 7]
def baseStart_478501 : Nat := 118140960795 + 478501 * 2 ^ 59
def prefixEnd_478501 : Nat := 4983230072969 + 3 ^ 40 * 478501 * 2
def baseEnd_478501 : Nat := 36400149134390755012877

theorem tailTrace_478501 : CollatzResearch.WordTrace tailWord_478501 prefixEnd_478501 36400149134390755012877 := by
  unfold tailWord_478501
  simp only [CollatzResearch.WordTrace]
  refine ⟨17452365239480073309731357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11634910159653382206487571 17452365239480073309731357)
  ·
    refine ⟨6544636964805027491149259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17452365239480073309731357 6544636964805027491149259)
    ·
      refine ⟨9816955447207541236723889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6544636964805027491149259 9816955447207541236723889)
      ·
        refine ⟨7362716585405655927542917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9816955447207541236723889 7362716585405655927542917)
        ·
          refine ⟨1380509359763560486414297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7362716585405655927542917 1380509359763560486414297)
          ·
            refine ⟨1035382019822670364810723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1380509359763560486414297 1035382019822670364810723)
            ·
              refine ⟨1553073029734005547216085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035382019822670364810723 1553073029734005547216085)
              ·
                refine ⟨36400149134390755012877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1553073029734005547216085 36400149134390755012877)
                ·
                  rfl

theorem cell21_478501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 7].length) (baseStart_478501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_478501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_478501 prefixEnd_478501 := by exact prefixLift 478501
  have htrace : WordTrace (prefixWord ++ tailWord_478501) baseStart_478501 baseEnd_478501 := by
    simpa [prefixWord, tailWord_478501, baseEnd_478501] using wordTrace_append hprefix tailTrace_478501
  have hstable : (prefixWord ++ tailWord_478501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478501).length < 2 ^ (prefixWord ++ tailWord_478501).sum := by decide
  have hdescent : baseEnd_478501 < baseStart_478501 := by decide
  rcases family_descends (prefixWord ++ tailWord_478501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478667 : List Nat := [1, 1, 1, 1, 3, 3, 4, 2, 5]
def baseStart_478667 : Nat := 118140960795 + 478667 * 2 ^ 59
def prefixEnd_478667 : Nat := 4983230072969 + 3 ^ 40 * 478667 * 2
def baseEnd_478667 : Nat := 109238330864792865271625

theorem tailTrace_478667 : CollatzResearch.WordTrace tailWord_478667 prefixEnd_478667 109238330864792865271625 := by
  unfold tailWord_478667
  simp only [CollatzResearch.WordTrace]
  refine ⟨17458419756878683660274255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11638946504585789106849503 17458419756878683660274255)
  ·
    refine ⟨26187629635318025490411383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17458419756878683660274255 26187629635318025490411383)
    ·
      refine ⟨39281444452977038235617075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26187629635318025490411383 39281444452977038235617075)
      ·
        refine ⟨58922166679465557353425613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39281444452977038235617075 58922166679465557353425613)
        ·
          refine ⟨22095812504799584007534605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58922166679465557353425613 22095812504799584007534605)
          ·
            refine ⟨8285929689299844002825477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22095812504799584007534605 8285929689299844002825477)
            ·
              refine ⟨1553611816743720750529777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8285929689299844002825477 1553611816743720750529777)
              ·
                refine ⟨1165208862557790562897333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1553611816743720750529777 1165208862557790562897333)
                ·
                  refine ⟨109238330864792865271625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1165208862557790562897333 109238330864792865271625)
                  ·
                    rfl

theorem cell21_478667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 5].length) (baseStart_478667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_478667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_478667 prefixEnd_478667 := by exact prefixLift 478667
  have htrace : WordTrace (prefixWord ++ tailWord_478667) baseStart_478667 baseEnd_478667 := by
    simpa [prefixWord, tailWord_478667, baseEnd_478667] using wordTrace_append hprefix tailTrace_478667
  have hstable : (prefixWord ++ tailWord_478667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478667).length < 2 ^ (prefixWord ++ tailWord_478667).sum := by decide
  have hdescent : baseEnd_478667 < baseStart_478667 := by decide
  rcases family_descends (prefixWord ++ tailWord_478667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478712 : List Nat := [2, 1, 2, 1, 1, 5, 1, 8]
def baseStart_478712 : Nat := 118140960795 + 478712 * 2 ^ 59
def prefixEnd_478712 : Nat := 4983230072969 + 3 ^ 40 * 478712 * 2
def baseEnd_478712 : Nat := 36416200159294262340511

theorem tailTrace_478712 : CollatzResearch.WordTrace tailWord_478712 prefixEnd_478712 36416200159294262340511 := by
  unfold tailWord_478712
  simp only [CollatzResearch.WordTrace]
  refine ⟨8730030520857828172831195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11640040694477104230441593 8730030520857828172831195)
  ·
    refine ⟨13095045781286742259246793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8730030520857828172831195 13095045781286742259246793)
    ·
      refine ⟨9821284335965056694435095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13095045781286742259246793 9821284335965056694435095)
      ·
        refine ⟨14731926503947585041652643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9821284335965056694435095 14731926503947585041652643)
        ·
          refine ⟨22097889755921377562478965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14731926503947585041652643 22097889755921377562478965)
          ·
            refine ⟨2071677164617629146482403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22097889755921377562478965 2071677164617629146482403)
            ·
              refine ⟨3107515746926443719723605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2071677164617629146482403 3107515746926443719723605)
              ·
                refine ⟨36416200159294262340511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3107515746926443719723605 36416200159294262340511)
                ·
                  rfl

theorem cell21_478712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 8].length) (baseStart_478712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_478712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_478712 prefixEnd_478712 := by exact prefixLift 478712
  have htrace : WordTrace (prefixWord ++ tailWord_478712) baseStart_478712 baseEnd_478712 := by
    simpa [prefixWord, tailWord_478712, baseEnd_478712] using wordTrace_append hprefix tailTrace_478712
  have hstable : (prefixWord ++ tailWord_478712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478712).length < 2 ^ (prefixWord ++ tailWord_478712).sum := by decide
  have hdescent : baseEnd_478712 < baseStart_478712 := by decide
  rcases family_descends (prefixWord ++ tailWord_478712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478819 : List Nat := [1, 1, 1, 5, 1, 3, 1, 3, 5]
def baseStart_478819 : Nat := 118140960795 + 478819 * 2 ^ 59
def prefixEnd_478819 : Nat := 4983230072969 + 3 ^ 40 * 478819 * 2
def baseEnd_478819 : Nat := 109273019335674378737981

theorem tailTrace_478819 : CollatzResearch.WordTrace tailWord_478819 prefixEnd_478819 109273019335674378737981 := by
  unfold tailWord_478819
  simp only [CollatzResearch.WordTrace]
  refine ⟨17463963652328013619807511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11642642434885342413205007 17463963652328013619807511)
  ·
    refine ⟨26195945478492020429711267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17463963652328013619807511 26195945478492020429711267)
    ·
      refine ⟨39293918217738030644566901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26195945478492020429711267 39293918217738030644566901)
      ·
        refine ⟨3683804832912940372928147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39293918217738030644566901 3683804832912940372928147)
        ·
          refine ⟨5525707249369410559392221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3683804832912940372928147 5525707249369410559392221)
          ·
            refine ⟨2072140218513528959772083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5525707249369410559392221 2072140218513528959772083)
            ·
              refine ⟨3108210327770293439658125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2072140218513528959772083 3108210327770293439658125)
              ·
                refine ⟨1165578872913860039871797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3108210327770293439658125 1165578872913860039871797)
                ·
                  refine ⟨109273019335674378737981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1165578872913860039871797 109273019335674378737981)
                  ·
                    rfl

theorem cell21_478819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 5].length) (baseStart_478819 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_478819 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_478819 prefixEnd_478819 := by exact prefixLift 478819
  have htrace : WordTrace (prefixWord ++ tailWord_478819) baseStart_478819 baseEnd_478819 := by
    simpa [prefixWord, tailWord_478819, baseEnd_478819] using wordTrace_append hprefix tailTrace_478819
  have hstable : (prefixWord ++ tailWord_478819).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478819).length < 2 ^ (prefixWord ++ tailWord_478819).sum := by decide
  have hdescent : baseEnd_478819 < baseStart_478819 := by decide
  rcases family_descends (prefixWord ++ tailWord_478819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478881 : List Nat := [1, 2, 3, 3, 2, 2, 2, 6]
def baseStart_478881 : Nat := 118140960795 + 478881 * 2 ^ 59
def prefixEnd_478881 : Nat := 4983230072969 + 3 ^ 40 * 478881 * 2
def baseEnd_478881 : Nat := 36429056193458682901507

theorem tailTrace_478881 : CollatzResearch.WordTrace tailWord_478881 prefixEnd_478881 36429056193458682901507 := by
  unfold tailWord_478881
  simp only [CollatzResearch.WordTrace]
  refine ⟨17466224978103398208564497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11644149985402265472376331 17466224978103398208564497)
  ·
    refine ⟨13099668733577548656423373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17466224978103398208564497 13099668733577548656423373)
    ·
      refine ⟨4912375775091580746158765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13099668733577548656423373 4912375775091580746158765)
      ·
        refine ⟨1842140915659342779809537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4912375775091580746158765 1842140915659342779809537)
        ·
          refine ⟨1381605686744507084857153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1842140915659342779809537 1381605686744507084857153)
          ·
            refine ⟨1036204265058380313642865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1381605686744507084857153 1036204265058380313642865)
            ·
              refine ⟨777153198793785235232149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1036204265058380313642865 777153198793785235232149)
              ·
                refine ⟨36429056193458682901507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 777153198793785235232149 36429056193458682901507)
                ·
                  rfl

theorem cell21_478881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 6].length) (baseStart_478881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_478881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_478881 prefixEnd_478881 := by exact prefixLift 478881
  have htrace : WordTrace (prefixWord ++ tailWord_478881) baseStart_478881 baseEnd_478881 := by
    simpa [prefixWord, tailWord_478881, baseEnd_478881] using wordTrace_append hprefix tailTrace_478881
  have hstable : (prefixWord ++ tailWord_478881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478881).length < 2 ^ (prefixWord ++ tailWord_478881).sum := by decide
  have hdescent : baseEnd_478881 < baseStart_478881 := by decide
  rcases family_descends (prefixWord ++ tailWord_478881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478884 : List Nat := [2, 3, 1, 2, 2, 4, 2, 1, 4]
def baseStart_478884 : Nat := 118140960795 + 478884 * 2 ^ 59
def prefixEnd_478884 : Nat := 4983230072969 + 3 ^ 40 * 478884 * 2
def baseEnd_478884 : Nat := 109287853221248710154515

theorem tailTrace_478884 : CollatzResearch.WordTrace tailWord_478884 prefixEnd_478884 109287853221248710154515 := by
  unfold tailWord_478884
  simp only [CollatzResearch.WordTrace]
  refine ⟨8733167198546264860461853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11644222931395019813949137 8733167198546264860461853)
  ·
    refine ⟨3274937699454849322673195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8733167198546264860461853 3274937699454849322673195)
    ·
      refine ⟨4912406549182273984009793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3274937699454849322673195 4912406549182273984009793)
      ·
        refine ⟨3684304911886705488007345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4912406549182273984009793 3684304911886705488007345)
        ·
          refine ⟨2763228683915029116005509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3684304911886705488007345 2763228683915029116005509)
          ·
            refine ⟨518105378234067959251033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2763228683915029116005509 518105378234067959251033)
            ·
              refine ⟨388579033675550969438275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518105378234067959251033 388579033675550969438275)
              ·
                refine ⟨582868550513326454157413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388579033675550969438275 582868550513326454157413)
                ·
                  refine ⟨109287853221248710154515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 582868550513326454157413 109287853221248710154515)
                  ·
                    rfl

theorem cell21_478884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_478884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_478884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_478884 prefixEnd_478884 := by exact prefixLift 478884
  have htrace : WordTrace (prefixWord ++ tailWord_478884) baseStart_478884 baseEnd_478884 := by
    simpa [prefixWord, tailWord_478884, baseEnd_478884] using wordTrace_append hprefix tailTrace_478884
  have hstable : (prefixWord ++ tailWord_478884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478884).length < 2 ^ (prefixWord ++ tailWord_478884).sum := by decide
  have hdescent : baseEnd_478884 < baseStart_478884 := by decide
  rcases family_descends (prefixWord ++ tailWord_478884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478912 : List Nat := [2, 1, 1, 2, 4, 1, 2, 5, 3]
def baseStart_478912 : Nat := 118140960795 + 478912 * 2 ^ 59
def prefixEnd_478912 : Nat := 4983230072969 + 3 ^ 40 * 478912 * 2
def baseEnd_478912 : Nat := 109294243202726883687791

theorem tailTrace_478912 : CollatzResearch.WordTrace tailWord_478912 prefixEnd_478912 109294243202726883687791 := by
  unfold tailWord_478912
  simp only [CollatzResearch.WordTrace]
  refine ⟨8733677820495545251471495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11644903760660727001961993 8733677820495545251471495)
  ·
    refine ⟨13100516730743317877207243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8733677820495545251471495 13100516730743317877207243)
    ·
      refine ⟨19650775096114976815810865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13100516730743317877207243 19650775096114976815810865)
      ·
        refine ⟨14738081322086232611858149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19650775096114976815810865 14738081322086232611858149)
        ·
          refine ⟨2763390247891168614723403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14738081322086232611858149 2763390247891168614723403)
          ·
            refine ⟨4145085371836752922085105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2763390247891168614723403 4145085371836752922085105)
            ·
              refine ⟨3108814028877564691563829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4145085371836752922085105 3108814028877564691563829)
              ·
                refine ⟨291451315207271689834109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3108814028877564691563829 291451315207271689834109)
                ·
                  refine ⟨109294243202726883687791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 291451315207271689834109 109294243202726883687791)
                  ·
                    rfl

theorem cell21_478912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 5, 3].length) (baseStart_478912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_478912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_478912 prefixEnd_478912 := by exact prefixLift 478912
  have htrace : WordTrace (prefixWord ++ tailWord_478912) baseStart_478912 baseEnd_478912 := by
    simpa [prefixWord, tailWord_478912, baseEnd_478912] using wordTrace_append hprefix tailTrace_478912
  have hstable : (prefixWord ++ tailWord_478912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478912).length < 2 ^ (prefixWord ++ tailWord_478912).sum := by decide
  have hdescent : baseEnd_478912 < baseStart_478912 := by decide
  rcases family_descends (prefixWord ++ tailWord_478912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478929 : List Nat := [1, 2, 2, 1, 2, 4, 4, 2, 3]
def baseStart_478929 : Nat := 118140960795 + 478929 * 2 ^ 59
def prefixEnd_478929 : Nat := 4983230072969 + 3 ^ 40 * 478929 * 2
def baseEnd_478929 : Nat := 109298122834338631904423

theorem tailTrace_478929 : CollatzResearch.WordTrace tailWord_478929 prefixEnd_478929 109298122834338631904423 := by
  unfold tailWord_478929
  simp only [CollatzResearch.WordTrace]
  refine ⟨17467975681929502406311841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11645317121286334937541227 17467975681929502406311841)
  ·
    refine ⟨13100981761447126804733881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17467975681929502406311841 13100981761447126804733881)
    ·
      refine ⟨9825736321085345103550411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13100981761447126804733881 9825736321085345103550411)
      ·
        refine ⟨14738604481628017655325617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9825736321085345103550411 14738604481628017655325617)
        ·
          refine ⟨11053953361221013241494213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14738604481628017655325617 11053953361221013241494213)
          ·
            refine ⟨2072616255228939982780165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11053953361221013241494213 2072616255228939982780165)
            ·
              refine ⟨388615547855426246771281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2072616255228939982780165 388615547855426246771281)
              ·
                refine ⟨291461660891569685078461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 388615547855426246771281 291461660891569685078461)
                ·
                  refine ⟨109298122834338631904423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 291461660891569685078461 109298122834338631904423)
                  ·
                    rfl

theorem cell21_478929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 2, 3].length) (baseStart_478929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_478929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_478929 prefixEnd_478929 := by exact prefixLift 478929
  have htrace : WordTrace (prefixWord ++ tailWord_478929) baseStart_478929 baseEnd_478929 := by
    simpa [prefixWord, tailWord_478929, baseEnd_478929] using wordTrace_append hprefix tailTrace_478929
  have hstable : (prefixWord ++ tailWord_478929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478929).length < 2 ^ (prefixWord ++ tailWord_478929).sum := by decide
  have hdescent : baseEnd_478929 < baseStart_478929 := by decide
  rcases family_descends (prefixWord ++ tailWord_478929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478988 : List Nat := [2, 2, 1, 2, 2, 1, 4, 4, 3]
def baseStart_478988 : Nat := 118140960795 + 478988 * 2 ^ 59
def prefixEnd_478988 : Nat := 4983230072969 + 3 ^ 40 * 478988 * 2
def baseEnd_478988 : Nat := 109311587438167640420969

theorem tailTrace_478988 : CollatzResearch.WordTrace tailWord_478988 prefixEnd_478988 109311587438167640420969 := by
  unfold tailWord_478988
  simp only [CollatzResearch.WordTrace]
  refine ⟨8735063794357877741354809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11646751725810503655139745 8735063794357877741354809)
  ·
    refine ⟨6551297845768408306016107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8735063794357877741354809 6551297845768408306016107)
    ·
      refine ⟨9826946768652612459024161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6551297845768408306016107 9826946768652612459024161)
      ·
        refine ⟨7370210076489459344268121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9826946768652612459024161 7370210076489459344268121)
        ·
          refine ⟨5527657557367094508201091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7370210076489459344268121 5527657557367094508201091)
          ·
            refine ⟨8291486336050641762301637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5527657557367094508201091 8291486336050641762301637)
            ·
              refine ⟨1554653688009495330431557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8291486336050641762301637 1554653688009495330431557)
              ·
                refine ⟨291497566501780374455917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1554653688009495330431557 291497566501780374455917)
                ·
                  refine ⟨109311587438167640420969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 291497566501780374455917 109311587438167640420969)
                  ·
                    rfl

theorem cell21_478988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 4, 3].length) (baseStart_478988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_478988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_478988 prefixEnd_478988 := by exact prefixLift 478988
  have htrace : WordTrace (prefixWord ++ tailWord_478988) baseStart_478988 baseEnd_478988 := by
    simpa [prefixWord, tailWord_478988, baseEnd_478988] using wordTrace_append hprefix tailTrace_478988
  have hstable : (prefixWord ++ tailWord_478988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478988).length < 2 ^ (prefixWord ++ tailWord_478988).sum := by decide
  have hdescent : baseEnd_478988 < baseStart_478988 := by decide
  rcases family_descends (prefixWord ++ tailWord_478988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479047 : List Nat := [1, 1, 4, 1, 2, 1, 5, 1, 5]
def baseStart_479047 : Nat := 118140960795 + 479047 * 2 ^ 59
def prefixEnd_479047 : Nat := 4983230072969 + 3 ^ 40 * 479047 * 2
def baseEnd_479047 : Nat := 109325052041996648937515

theorem tailTrace_479047 : CollatzResearch.WordTrace tailWord_479047 prefixEnd_479047 109325052041996648937515 := by
  unfold tailWord_479047
  simp only [CollatzResearch.WordTrace]
  refine ⟨17472279495502008559107395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11648186330334672372738263 17472279495502008559107395)
  ·
    refine ⟨26208419243253012838661093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17472279495502008559107395 26208419243253012838661093)
    ·
      refine ⟨4914078608109939907248955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26208419243253012838661093 4914078608109939907248955)
      ·
        refine ⟨7371117912164909860873433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4914078608109939907248955 7371117912164909860873433)
        ·
          refine ⟨5528338434123682395655075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7371117912164909860873433 5528338434123682395655075)
          ·
            refine ⟨8292507651185523593482613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5528338434123682395655075 8292507651185523593482613)
            ·
              refine ⟨777422592298642836888995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8292507651185523593482613 777422592298642836888995)
              ·
                refine ⟨1166133888447964255333493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 777422592298642836888995 1166133888447964255333493)
                ·
                  refine ⟨109325052041996648937515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1166133888447964255333493 109325052041996648937515)
                  ·
                    rfl

theorem cell21_479047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 5].length) (baseStart_479047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_479047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_479047 prefixEnd_479047 := by exact prefixLift 479047
  have htrace : WordTrace (prefixWord ++ tailWord_479047) baseStart_479047 baseEnd_479047 := by
    simpa [prefixWord, tailWord_479047, baseEnd_479047] using wordTrace_append hprefix tailTrace_479047
  have hstable : (prefixWord ++ tailWord_479047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479047).length < 2 ^ (prefixWord ++ tailWord_479047).sum := by decide
  have hdescent : baseEnd_479047 < baseStart_479047 := by decide
  rcases family_descends (prefixWord ++ tailWord_479047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479053 : List Nat := [1, 6, 1, 2, 1, 3, 2, 1, 4]
def baseStart_479053 : Nat := 118140960795 + 479053 * 2 ^ 59
def prefixEnd_479053 : Nat := 4983230072969 + 3 ^ 40 * 479053 * 2
def baseEnd_479053 : Nat := 109326421323741971837503

theorem tailTrace_479053 : CollatzResearch.WordTrace tailWord_479053 prefixEnd_479053 109326421323741971837503 := by
  unfold tailWord_479053
  simp only [CollatzResearch.WordTrace]
  refine ⟨17472498333480271583825813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11648332222320181055883875 17472498333480271583825813)
  ·
    refine ⟨819023359381887730491835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17472498333480271583825813 819023359381887730491835)
    ·
      refine ⟨1228535039072831595737753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 819023359381887730491835 1228535039072831595737753)
      ·
        refine ⟨921401279304623696803315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1228535039072831595737753 921401279304623696803315)
        ·
          refine ⟨1382101918956935545204973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 921401279304623696803315 1382101918956935545204973)
          ·
            refine ⟨518288219608850829451865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1382101918956935545204973 518288219608850829451865)
            ·
              refine ⟨388716164706638122088899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518288219608850829451865 388716164706638122088899)
              ·
                refine ⟨583074247059957183133349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388716164706638122088899 583074247059957183133349)
                ·
                  refine ⟨109326421323741971837503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 583074247059957183133349 109326421323741971837503)
                  ·
                    rfl

theorem cell21_479053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_479053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_479053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_479053 prefixEnd_479053 := by exact prefixLift 479053
  have htrace : WordTrace (prefixWord ++ tailWord_479053) baseStart_479053 baseEnd_479053 := by
    simpa [prefixWord, tailWord_479053, baseEnd_479053] using wordTrace_append hprefix tailTrace_479053
  have hstable : (prefixWord ++ tailWord_479053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479053).length < 2 ^ (prefixWord ++ tailWord_479053).sum := by decide
  have hdescent : baseEnd_479053 < baseStart_479053 := by decide
  rcases family_descends (prefixWord ++ tailWord_479053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479140 : List Nat := [2, 3, 1, 2, 1, 3, 1, 5, 3]
def baseStart_479140 : Nat := 118140960795 + 479140 * 2 ^ 59
def prefixEnd_479140 : Nat := 4983230072969 + 3 ^ 40 * 479140 * 2
def baseEnd_479140 : Nat := 109346275909049153887325

theorem tailTrace_479140 : CollatzResearch.WordTrace tailWord_479140 prefixEnd_479140 109346275909049153887325 := by
  unfold tailWord_479140
  simp only [CollatzResearch.WordTrace]
  refine ⟨8737835742082542721121437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11650447656110056961495249 8737835742082542721121437)
  ·
    refine ⟨3276688403280953520420539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8737835742082542721121437 3276688403280953520420539)
    ·
      refine ⟨4915032604921430280630809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3276688403280953520420539 4915032604921430280630809)
      ·
        refine ⟨3686274453691072710473107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4915032604921430280630809 3686274453691072710473107)
        ·
          refine ⟨5529411680536609065709661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3686274453691072710473107 5529411680536609065709661)
          ·
            refine ⟨2073529380201228399641123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5529411680536609065709661 2073529380201228399641123)
            ·
              refine ⟨3110294070301842599461685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2073529380201228399641123 3110294070301842599461685)
              ·
                refine ⟨291590069090797743699533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3110294070301842599461685 291590069090797743699533)
                ·
                  refine ⟨109346275909049153887325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 291590069090797743699533 109346275909049153887325)
                  ·
                    rfl

theorem cell21_479140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_479140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_479140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_479140 prefixEnd_479140 := by exact prefixLift 479140
  have htrace : WordTrace (prefixWord ++ tailWord_479140) baseStart_479140 baseEnd_479140 := by
    simpa [prefixWord, tailWord_479140, baseEnd_479140] using wordTrace_append hprefix tailTrace_479140
  have hstable : (prefixWord ++ tailWord_479140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479140).length < 2 ^ (prefixWord ++ tailWord_479140).sum := by decide
  have hdescent : baseEnd_479140 < baseStart_479140 := by decide
  rcases family_descends (prefixWord ++ tailWord_479140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479151 : List Nat := [1, 1, 2, 1, 2, 2, 12]
def baseStart_479151 : Nat := 118140960795 + 479151 * 2 ^ 59
def prefixEnd_479151 : Nat := 4983230072969 + 3 ^ 40 * 479151 * 2
def baseEnd_479151 : Nat := 12149865139879508800441

theorem tailTrace_479151 : CollatzResearch.WordTrace tailWord_479151 prefixEnd_479151 12149865139879508800441 := by
  unfold tailWord_479151
  simp only [CollatzResearch.WordTrace]
  refine ⟨17476072687125234320893307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11650715124750156213928871 17476072687125234320893307)
  ·
    refine ⟨26214109030687851481339961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17476072687125234320893307 26214109030687851481339961)
    ·
      refine ⟨19660581773015888611004971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26214109030687851481339961 19660581773015888611004971)
      ·
        refine ⟨29490872659523832916507457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19660581773015888611004971 29490872659523832916507457)
        ·
          refine ⟨22118154494642874687380593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29490872659523832916507457 22118154494642874687380593)
          ·
            refine ⟨16588615870982156015535445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22118154494642874687380593 16588615870982156015535445)
            ·
              refine ⟨12149865139879508800441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 16588615870982156015535445 12149865139879508800441)
              ·
                rfl

theorem cell21_479151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 12].length) (baseStart_479151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_479151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_479151 prefixEnd_479151 := by exact prefixLift 479151
  have htrace : WordTrace (prefixWord ++ tailWord_479151) baseStart_479151 baseEnd_479151 := by
    simpa [prefixWord, tailWord_479151, baseEnd_479151] using wordTrace_append hprefix tailTrace_479151
  have hstable : (prefixWord ++ tailWord_479151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479151).length < 2 ^ (prefixWord ++ tailWord_479151).sum := by decide
  have hdescent : baseEnd_479151 < baseStart_479151 := by decide
  rcases family_descends (prefixWord ++ tailWord_479151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479202 : List Nat := [3, 3, 3, 1, 2, 2, 7]
def baseStart_479202 : Nat := 118140960795 + 479202 * 2 ^ 59
def prefixEnd_479202 : Nat := 4983230072969 + 3 ^ 40 * 479202 * 2
def baseEnd_479202 : Nat := 12151158350416758205985

theorem tailTrace_479202 : CollatzResearch.WordTrace tailWord_479202 prefixEnd_479202 12151158350416758205985 := by
  unfold tailWord_479202
  simp only [CollatzResearch.WordTrace]
  refine ⟨4369483202485117507749965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11651955206626980020666573 4369483202485117507749965)
  ·
    refine ⟨1638556200931919065406237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4369483202485117507749965 1638556200931919065406237)
    ·
      refine ⟨614458575349469649527339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1638556200931919065406237 614458575349469649527339)
      ·
        refine ⟨921687863024204474291009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614458575349469649527339 921687863024204474291009)
        ·
          refine ⟨691265897268153355718257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 921687863024204474291009 691265897268153355718257)
          ·
            refine ⟨518449422951115016788693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 691265897268153355718257 518449422951115016788693)
            ·
              refine ⟨12151158350416758205985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 518449422951115016788693 12151158350416758205985)
              ·
                rfl

theorem cell21_479202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 7].length) (baseStart_479202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_479202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_479202 prefixEnd_479202 := by exact prefixLift 479202
  have htrace : WordTrace (prefixWord ++ tailWord_479202) baseStart_479202 baseEnd_479202 := by
    simpa [prefixWord, tailWord_479202, baseEnd_479202] using wordTrace_append hprefix tailTrace_479202
  have hstable : (prefixWord ++ tailWord_479202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479202).length < 2 ^ (prefixWord ++ tailWord_479202).sum := by decide
  have hdescent : baseEnd_479202 < baseStart_479202 := by decide
  rcases family_descends (prefixWord ++ tailWord_479202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479227 : List Nat := [1, 1, 1, 1, 1, 3, 5, 8]
def baseStart_479227 : Nat := 118140960795 + 479227 * 2 ^ 59
def prefixEnd_479227 : Nat := 4983230072969 + 3 ^ 40 * 479227 * 2
def baseEnd_479227 : Nat := 36455376831452111979049

theorem tailTrace_479227 : CollatzResearch.WordTrace tailWord_479227 prefixEnd_479227 36455376831452111979049 := by
  unfold tailWord_479227
  simp only [CollatzResearch.WordTrace]
  refine ⟨17478844634849899300659935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11652563089899932867106623 17478844634849899300659935)
  ·
    refine ⟨26218266952274848950989903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17478844634849899300659935 26218266952274848950989903)
    ·
      refine ⟨39327400428412273426484855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26218266952274848950989903 39327400428412273426484855)
      ·
        refine ⟨58991100642618410139727283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39327400428412273426484855 58991100642618410139727283)
        ·
          refine ⟨88486650963927615209590925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58991100642618410139727283 88486650963927615209590925)
          ·
            refine ⟨33182494111472855703596597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88486650963927615209590925 33182494111472855703596597)
            ·
              refine ⟨3110858822950580222212181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33182494111472855703596597 3110858822950580222212181)
              ·
                refine ⟨36455376831452111979049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3110858822950580222212181 36455376831452111979049)
                ·
                  rfl

theorem cell21_479227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 8].length) (baseStart_479227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_479227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_479227 prefixEnd_479227 := by exact prefixLift 479227
  have htrace : WordTrace (prefixWord ++ tailWord_479227) baseStart_479227 baseEnd_479227 := by
    simpa [prefixWord, tailWord_479227, baseEnd_479227] using wordTrace_append hprefix tailTrace_479227
  have hstable : (prefixWord ++ tailWord_479227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479227).length < 2 ^ (prefixWord ++ tailWord_479227).sum := by decide
  have hdescent : baseEnd_479227 < baseStart_479227 := by decide
  rcases family_descends (prefixWord ++ tailWord_479227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479309 : List Nat := [1, 6, 1, 1, 1, 1, 4, 3, 3]
def baseStart_479309 : Nat := 118140960795 + 479309 * 2 ^ 59
def prefixEnd_479309 : Nat := 4983230072969 + 3 ^ 40 * 479309 * 2
def baseEnd_479309 : Nat := 109384844011542415570313

theorem tailTrace_479309 : CollatzResearch.WordTrace tailWord_479309 prefixEnd_479309 109384844011542415570313 := by
  unfold tailWord_479309
  simp only [CollatzResearch.WordTrace]
  refine ⟨17481835420552827305144981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11654556947035218203429987 17481835420552827305144981)
  ·
    refine ⟨819461035338413779928671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17481835420552827305144981 819461035338413779928671)
    ·
      refine ⟨1229191553007620669893007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 819461035338413779928671 1229191553007620669893007)
      ·
        refine ⟨1843787329511431004839511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1229191553007620669893007 1843787329511431004839511)
        ·
          refine ⟨2765680994267146507259267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1843787329511431004839511 2765680994267146507259267)
          ·
            refine ⟨4148521491400719760888901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2765680994267146507259267 4148521491400719760888901)
            ·
              refine ⟨777847779637634955166669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4148521491400719760888901 777847779637634955166669)
              ·
                refine ⟨291692917364113108187501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 777847779637634955166669 291692917364113108187501)
                ·
                  refine ⟨109384844011542415570313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 291692917364113108187501 109384844011542415570313)
                  ·
                    rfl

theorem cell21_479309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_479309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_479309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_479309 prefixEnd_479309 := by exact prefixLift 479309
  have htrace : WordTrace (prefixWord ++ tailWord_479309) baseStart_479309 baseEnd_479309 := by
    simpa [prefixWord, tailWord_479309, baseEnd_479309] using wordTrace_append hprefix tailTrace_479309
  have hstable : (prefixWord ++ tailWord_479309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479309).length < 2 ^ (prefixWord ++ tailWord_479309).sum := by decide
  have hdescent : baseEnd_479309 < baseStart_479309 := by decide
  rcases family_descends (prefixWord ++ tailWord_479309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479326 : List Nat := [4, 4, 1, 1, 2, 1, 2, 1, 5]
def baseStart_479326 : Nat := 118140960795 + 479326 * 2 ^ 59
def prefixEnd_479326 : Nat := 4983230072969 + 3 ^ 40 * 479326 * 2
def baseEnd_479326 : Nat := 109388723643154163786945

theorem tailTrace_479326 : CollatzResearch.WordTrace tailWord_479326 prefixEnd_479326 109388723643154163786945 := by
  unfold tailWord_479326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2185306932686404901064229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11654970307660826139009221 2185306932686404901064229)
  ·
    refine ⟨409745049878700918949543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2185306932686404901064229 409745049878700918949543)
    ·
      refine ⟨614617574818051378424315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409745049878700918949543 614617574818051378424315)
      ·
        refine ⟨921926362227077067636473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614617574818051378424315 921926362227077067636473)
        ·
          refine ⟨691444771670307800727355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 921926362227077067636473 691444771670307800727355)
          ·
            refine ⟨1037167157505461701091033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691444771670307800727355 1037167157505461701091033)
            ·
              refine ⟨777875368129096275818275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1037167157505461701091033 777875368129096275818275)
              ·
                refine ⟨1166813052193644413727413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 777875368129096275818275 1166813052193644413727413)
                ·
                  refine ⟨109388723643154163786945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1166813052193644413727413 109388723643154163786945)
                  ·
                    rfl

theorem cell21_479326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_479326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_479326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_479326 prefixEnd_479326 := by exact prefixLift 479326
  have htrace : WordTrace (prefixWord ++ tailWord_479326) baseStart_479326 baseEnd_479326 := by
    simpa [prefixWord, tailWord_479326, baseEnd_479326] using wordTrace_append hprefix tailTrace_479326
  have hstable : (prefixWord ++ tailWord_479326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479326).length < 2 ^ (prefixWord ++ tailWord_479326).sum := by decide
  have hdescent : baseEnd_479326 < baseStart_479326 := by decide
  rcases family_descends (prefixWord ++ tailWord_479326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479365 : List Nat := [1, 3, 1, 1, 5, 1, 1, 2, 6]
def baseStart_479365 : Nat := 118140960795 + 479365 * 2 ^ 59
def prefixEnd_479365 : Nat := 4983230072969 + 3 ^ 40 * 479365 * 2
def baseEnd_479365 : Nat := 109397623974498762636865

theorem tailTrace_479365 : CollatzResearch.WordTrace tailWord_479365 prefixEnd_479365 109397623974498762636865 := by
  unfold tailWord_479365
  simp only [CollatzResearch.WordTrace]
  refine ⟨17483877908349948869183549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11655918605566632579455699 17483877908349948869183549)
  ·
    refine ⟨6556454215631230825943831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17483877908349948869183549 6556454215631230825943831)
    ·
      refine ⟨9834681323446846238915747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6556454215631230825943831 9834681323446846238915747)
      ·
        refine ⟨14752021985170269358373621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9834681323446846238915747 14752021985170269358373621)
        ·
          refine ⟨1383002061109712752347527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14752021985170269358373621 1383002061109712752347527)
          ·
            refine ⟨2074503091664569128521291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1383002061109712752347527 2074503091664569128521291)
            ·
              refine ⟨3111754637496853692781937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2074503091664569128521291 3111754637496853692781937)
              ·
                refine ⟨2333815978122640269586453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3111754637496853692781937 2333815978122640269586453)
                ·
                  refine ⟨109397623974498762636865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2333815978122640269586453 109397623974498762636865)
                  ·
                    rfl

theorem cell21_479365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_479365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_479365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_479365 prefixEnd_479365 := by exact prefixLift 479365
  have htrace : WordTrace (prefixWord ++ tailWord_479365) baseStart_479365 baseEnd_479365 := by
    simpa [prefixWord, tailWord_479365, baseEnd_479365] using wordTrace_append hprefix tailTrace_479365
  have hstable : (prefixWord ++ tailWord_479365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479365).length < 2 ^ (prefixWord ++ tailWord_479365).sum := by decide
  have hdescent : baseEnd_479365 < baseStart_479365 := by decide
  rcases family_descends (prefixWord ++ tailWord_479365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479399 : List Nat := [1, 1, 6, 2, 2, 1, 1, 3, 4]
def baseStart_479399 : Nat := 118140960795 + 479399 * 2 ^ 59
def prefixEnd_479399 : Nat := 4983230072969 + 3 ^ 40 * 479399 * 2
def baseEnd_479399 : Nat := 109405383237722259070129

theorem tailTrace_479399 : CollatzResearch.WordTrace tailWord_479399 prefixEnd_479399 109405383237722259070129 := by
  unfold tailWord_479399
  simp only [CollatzResearch.WordTrace]
  refine ⟨17485117990226772675921251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11656745326817848450614167 17485117990226772675921251)
  ·
    refine ⟨26227676985340159013881877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17485117990226772675921251 26227676985340159013881877)
    ·
      refine ⟨1229422358687819953775713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26227676985340159013881877 1229422358687819953775713)
      ·
        refine ⟨922066769015864965331785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1229422358687819953775713 922066769015864965331785)
        ·
          refine ⟨691550076761898723998839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 922066769015864965331785 691550076761898723998839)
          ·
            refine ⟨1037325115142848085998259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691550076761898723998839 1037325115142848085998259)
            ·
              refine ⟨1555987672714272128997389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1037325115142848085998259 1555987672714272128997389)
              ·
                refine ⟨583495377267852048374021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1555987672714272128997389 583495377267852048374021)
                ·
                  refine ⟨109405383237722259070129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 583495377267852048374021 109405383237722259070129)
                  ·
                    rfl

theorem cell21_479399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 4].length) (baseStart_479399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_479399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_479399 prefixEnd_479399 := by exact prefixLift 479399
  have htrace : WordTrace (prefixWord ++ tailWord_479399) baseStart_479399 baseEnd_479399 := by
    simpa [prefixWord, tailWord_479399, baseEnd_479399] using wordTrace_append hprefix tailTrace_479399
  have hstable : (prefixWord ++ tailWord_479399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479399).length < 2 ^ (prefixWord ++ tailWord_479399).sum := by decide
  have hdescent : baseEnd_479399 < baseStart_479399 := by decide
  rcases family_descends (prefixWord ++ tailWord_479399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479410 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 7]
def baseStart_479410 : Nat := 118140960795 + 479410 * 2 ^ 59
def prefixEnd_479410 : Nat := 4983230072969 + 3 ^ 40 * 479410 * 2
def baseEnd_479410 : Nat := 109407893587588684386773

theorem tailTrace_479410 : CollatzResearch.WordTrace tailWord_479410 prefixEnd_479410 109407893587588684386773 := by
  unfold tailWord_479410
  simp only [CollatzResearch.WordTrace]
  refine ⟨4371379798296730388642921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11657012795457947703047789 4371379798296730388642921)
  ·
    refine ⟨3278534848722547791482191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4371379798296730388642921 3278534848722547791482191)
    ·
      refine ⟨4917802273083821687223287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3278534848722547791482191 4917802273083821687223287)
      ·
        refine ⟨7376703409625732530834931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4917802273083821687223287 7376703409625732530834931)
        ·
          refine ⟨11065055114438598796252397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7376703409625732530834931 11065055114438598796252397)
          ·
            refine ⟨4149395667914474548594649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11065055114438598796252397 4149395667914474548594649)
            ·
              refine ⟨3112046750935855911445987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4149395667914474548594649 3112046750935855911445987)
              ·
                refine ⟨4668070126403783867168981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3112046750935855911445987 4668070126403783867168981)
                ·
                  refine ⟨109407893587588684386773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4668070126403783867168981 109407893587588684386773)
                  ·
                    rfl

theorem cell21_479410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_479410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_479410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_479410 prefixEnd_479410 := by exact prefixLift 479410
  have htrace : WordTrace (prefixWord ++ tailWord_479410) baseStart_479410 baseEnd_479410 := by
    simpa [prefixWord, tailWord_479410, baseEnd_479410] using wordTrace_append hprefix tailTrace_479410
  have hstable : (prefixWord ++ tailWord_479410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479410).length < 2 ^ (prefixWord ++ tailWord_479410).sum := by decide
  have hdescent : baseEnd_479410 < baseStart_479410 := by decide
  rcases family_descends (prefixWord ++ tailWord_479410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479441 : List Nat := [1, 2, 2, 1, 2, 2, 3, 4, 4]
def baseStart_479441 : Nat := 118140960795 + 479441 * 2 ^ 59
def prefixEnd_479441 : Nat := 4983230072969 + 3 ^ 40 * 479441 * 2
def baseEnd_479441 : Nat := 109414968209939519370043

theorem tailTrace_479441 : CollatzResearch.WordTrace tailWord_479441 prefixEnd_479441 109414968209939519370043 := by
  unfold tailWord_479441
  simp only [CollatzResearch.WordTrace]
  refine ⟨17486649856074613848950177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11657766570716409232633451 17486649856074613848950177)
  ·
    refine ⟨13114987392055960386712633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17486649856074613848950177 13114987392055960386712633)
    ·
      refine ⟨9836240544041970290034475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13114987392055960386712633 9836240544041970290034475)
      ·
        refine ⟨14754360816062955435051713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9836240544041970290034475 14754360816062955435051713)
        ·
          refine ⟨11065770612047216576288785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14754360816062955435051713 11065770612047216576288785)
          ·
            refine ⟨8299327959035412432216589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11065770612047216576288785 8299327959035412432216589)
            ·
              refine ⟨3112247984638279662081221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8299327959035412432216589 3112247984638279662081221)
              ·
                refine ⟨583546497119677436640229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3112247984638279662081221 583546497119677436640229)
                ·
                  refine ⟨109414968209939519370043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 583546497119677436640229 109414968209939519370043)
                  ·
                    rfl

theorem cell21_479441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 4].length) (baseStart_479441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_479441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_479441 prefixEnd_479441 := by exact prefixLift 479441
  have htrace : WordTrace (prefixWord ++ tailWord_479441) baseStart_479441 baseEnd_479441 := by
    simpa [prefixWord, tailWord_479441, baseEnd_479441] using wordTrace_append hprefix tailTrace_479441
  have hstable : (prefixWord ++ tailWord_479441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479441).length < 2 ^ (prefixWord ++ tailWord_479441).sum := by decide
  have hdescent : baseEnd_479441 < baseStart_479441 := by decide
  rcases family_descends (prefixWord ++ tailWord_479441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479492 : List Nat := [2, 3, 2, 2, 4, 1, 1, 2, 4]
def baseStart_479492 : Nat := 118140960795 + 479492 * 2 ^ 59
def prefixEnd_479492 : Nat := 4983230072969 + 3 ^ 40 * 479492 * 2
def baseEnd_479492 : Nat := 109426607104774764019939

theorem tailTrace_479492 : CollatzResearch.WordTrace tailWord_479492 prefixEnd_479492 109426607104774764019939 := by
  unfold tailWord_479492
  simp only [CollatzResearch.WordTrace]
  refine ⟨8744254989444924779528365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11659006652593233039371153 8744254989444924779528365)
  ·
    refine ⟨3279095621041846792323137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8744254989444924779528365 3279095621041846792323137)
    ·
      refine ⟨2459321715781385094242353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3279095621041846792323137 2459321715781385094242353)
      ·
        refine ⟨1844491286836038820681765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2459321715781385094242353 1844491286836038820681765)
        ·
          refine ⟨345842116281757278877831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1844491286836038820681765 345842116281757278877831)
          ·
            refine ⟨518763174422635918316747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345842116281757278877831 518763174422635918316747)
            ·
              refine ⟨778144761633953877475121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518763174422635918316747 778144761633953877475121)
              ·
                refine ⟨583608571225465408106341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 778144761633953877475121 583608571225465408106341)
                ·
                  refine ⟨109426607104774764019939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 583608571225465408106341 109426607104774764019939)
                  ·
                    rfl

theorem cell21_479492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_479492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_479492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_479492 prefixEnd_479492 := by exact prefixLift 479492
  have htrace : WordTrace (prefixWord ++ tailWord_479492) baseStart_479492 baseEnd_479492 := by
    simpa [prefixWord, tailWord_479492, baseEnd_479492] using wordTrace_append hprefix tailTrace_479492
  have hstable : (prefixWord ++ tailWord_479492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479492).length < 2 ^ (prefixWord ++ tailWord_479492).sum := by decide
  have hdescent : baseEnd_479492 < baseStart_479492 := by decide
  rcases family_descends (prefixWord ++ tailWord_479492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479537 : List Nat := [1, 2, 2, 3, 4, 2, 1, 3, 3]
def baseStart_479537 : Nat := 118140960795 + 479537 * 2 ^ 59
def prefixEnd_479537 : Nat := 4983230072969 + 3 ^ 40 * 479537 * 2
def baseEnd_479537 : Nat := 109436876717864685769847

theorem tailTrace_479537 : CollatzResearch.WordTrace tailWord_479537 prefixEnd_479537 109436876717864685769847 := by
  unfold tailWord_479537
  simp only [CollatzResearch.WordTrace]
  refine ⟨17490151263726822244444865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11660100842484548162963243 17490151263726822244444865)
  ·
    refine ⟨13117613447795116683333649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17490151263726822244444865 13117613447795116683333649)
    ·
      refine ⟨9838210085846337512500237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13117613447795116683333649 9838210085846337512500237)
      ·
        refine ⟨3689328782192376567187589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9838210085846337512500237 3689328782192376567187589)
        ·
          refine ⟨691749146661070606347673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3689328782192376567187589 691749146661070606347673)
          ·
            refine ⟨518811859995802954760755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 691749146661070606347673 518811859995802954760755)
            ·
              refine ⟨778217789993704432141133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518811859995802954760755 778217789993704432141133)
              ·
                refine ⟨291831671247639162052925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 778217789993704432141133 291831671247639162052925)
                ·
                  refine ⟨109436876717864685769847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 291831671247639162052925 109436876717864685769847)
                  ·
                    rfl

theorem cell21_479537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 3, 3].length) (baseStart_479537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_479537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_479537 prefixEnd_479537 := by exact prefixLift 479537
  have htrace : WordTrace (prefixWord ++ tailWord_479537) baseStart_479537 baseEnd_479537 := by
    simpa [prefixWord, tailWord_479537, baseEnd_479537] using wordTrace_append hprefix tailTrace_479537
  have hstable : (prefixWord ++ tailWord_479537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479537).length < 2 ^ (prefixWord ++ tailWord_479537).sum := by decide
  have hdescent : baseEnd_479537 < baseStart_479537 := by decide
  rcases family_descends (prefixWord ++ tailWord_479537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479576 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 8]
def baseStart_479576 : Nat := 118140960795 + 479576 * 2 ^ 59
def prefixEnd_479576 : Nat := 4983230072969 + 3 ^ 40 * 479576 * 2
def baseEnd_479576 : Nat := 109445777049209284619767

theorem tailTrace_479576 : CollatzResearch.WordTrace tailWord_479576 prefixEnd_479576 109445777049209284619767 := by
  unfold tailWord_479576
  simp only [CollatzResearch.WordTrace]
  refine ⟨8745786855292765952557291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11661049140390354603409721 8745786855292765952557291)
  ·
    refine ⟨13118680282939148928835937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8745786855292765952557291 13118680282939148928835937)
    ·
      refine ⟨9839010212204361696626953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13118680282939148928835937 9839010212204361696626953)
      ·
        refine ⟨7379257659153271272470215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9839010212204361696626953 7379257659153271272470215)
        ·
          refine ⟨11068886488729906908705323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7379257659153271272470215 11068886488729906908705323)
          ·
            refine ⟨16603329733094860363057985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11068886488729906908705323 16603329733094860363057985)
            ·
              refine ⟨12452497299821145272293489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16603329733094860363057985 12452497299821145272293489)
              ·
                refine ⟨9339372974865858954220117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12452497299821145272293489 9339372974865858954220117)
                ·
                  refine ⟨109445777049209284619767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9339372974865858954220117 109445777049209284619767)
                  ·
                    rfl

theorem cell21_479576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 8].length) (baseStart_479576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_479576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_479576 prefixEnd_479576 := by exact prefixLift 479576
  have htrace : WordTrace (prefixWord ++ tailWord_479576) baseStart_479576 baseEnd_479576 := by
    simpa [prefixWord, tailWord_479576, baseEnd_479576] using wordTrace_append hprefix tailTrace_479576
  have hstable : (prefixWord ++ tailWord_479576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479576).length < 2 ^ (prefixWord ++ tailWord_479576).sum := by decide
  have hdescent : baseEnd_479576 < baseStart_479576 := by decide
  rcases family_descends (prefixWord ++ tailWord_479576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479613 : List Nat := [1, 4, 1, 1, 2, 5, 2, 2, 3]
def baseStart_479613 : Nat := 118140960795 + 479613 * 2 ^ 59
def prefixEnd_479613 : Nat := 4983230072969 + 3 ^ 40 * 479613 * 2
def baseEnd_479613 : Nat := 109454220953305442503025

theorem tailTrace_479613 : CollatzResearch.WordTrace tailWord_479613 prefixEnd_479613 109454220953305442503025 := by
  unfold tailWord_479613
  simp only [CollatzResearch.WordTrace]
  refine ⟨17492923211451487224211493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11661948807634324816140995 17492923211451487224211493)
  ·
    refine ⟨3279923102147153854539655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17492923211451487224211493 3279923102147153854539655)
    ·
      refine ⟨4919884653220730781809483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3279923102147153854539655 4919884653220730781809483)
      ·
        refine ⟨7379826979831096172714225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4919884653220730781809483 7379826979831096172714225)
        ·
          refine ⟨5534870234873322129535669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7379826979831096172714225 5534870234873322129535669)
          ·
            refine ⟨518894084519373949643969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5534870234873322129535669 518894084519373949643969)
            ·
              refine ⟨389170563389530462232977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518894084519373949643969 389170563389530462232977)
              ·
                refine ⟨291877922542147846674733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 389170563389530462232977 291877922542147846674733)
                ·
                  refine ⟨109454220953305442503025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 291877922542147846674733 109454220953305442503025)
                  ·
                    rfl

theorem cell21_479613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_479613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_479613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_479613 prefixEnd_479613 := by exact prefixLift 479613
  have htrace : WordTrace (prefixWord ++ tailWord_479613) baseStart_479613 baseEnd_479613 := by
    simpa [prefixWord, tailWord_479613, baseEnd_479613] using wordTrace_append hprefix tailTrace_479613
  have hstable : (prefixWord ++ tailWord_479613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479613).length < 2 ^ (prefixWord ++ tailWord_479613).sum := by decide
  have hdescent : baseEnd_479613 < baseStart_479613 := by decide
  rcases family_descends (prefixWord ++ tailWord_479613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479658 : List Nat := [3, 1, 6, 1, 1, 1, 8]
def baseStart_479658 : Nat := 118140960795 + 479658 * 2 ^ 59
def prefixEnd_479658 : Nat := 4983230072969 + 3 ^ 40 * 479658 * 2
def baseEnd_479658 : Nat := 12162721174043929361437

theorem tailTrace_479658 : CollatzResearch.WordTrace tailWord_479658 prefixEnd_479658 12162721174043929361437 := by
  unfold tailWord_479658
  simp only [CollatzResearch.WordTrace]
  refine ⟨4373641124072114977399907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11663042997525639939733085 4373641124072114977399907)
  ·
    refine ⟨6560461686108172466099861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4373641124072114977399907 6560461686108172466099861)
    ·
      refine ⟨307521641536320584348431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6560461686108172466099861 307521641536320584348431)
      ·
        refine ⟨461282462304480876522647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307521641536320584348431 461282462304480876522647)
        ·
          refine ⟨691923693456721314783971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461282462304480876522647 691923693456721314783971)
          ·
            refine ⟨1037885540185081972175957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691923693456721314783971 1037885540185081972175957)
            ·
              refine ⟨12162721174043929361437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1037885540185081972175957 12162721174043929361437)
              ·
                rfl

theorem cell21_479658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 8].length) (baseStart_479658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_479658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_479658 prefixEnd_479658 := by exact prefixLift 479658
  have htrace : WordTrace (prefixWord ++ tailWord_479658) baseStart_479658 baseEnd_479658 := by
    simpa [prefixWord, tailWord_479658, baseEnd_479658] using wordTrace_append hprefix tailTrace_479658
  have hstable : (prefixWord ++ tailWord_479658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479658).length < 2 ^ (prefixWord ++ tailWord_479658).sum := by decide
  have hdescent : baseEnd_479658 < baseStart_479658 := by decide
  rcases family_descends (prefixWord ++ tailWord_479658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479700 : List Nat := [2, 4, 1, 2, 2, 2, 1, 7]
def baseStart_479700 : Nat := 118140960795 + 479700 * 2 ^ 59
def prefixEnd_479700 : Nat := 4983230072969 + 3 ^ 40 * 479700 * 2
def baseEnd_479700 : Nat := 36491358512870874850949

theorem tailTrace_479700 : CollatzResearch.WordTrace tailWord_479700 prefixEnd_479700 36491358512870874850949 := by
  unfold tailWord_479700
  simp only [CollatzResearch.WordTrace]
  refine ⟨8748048181068150541314277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11664064241424200721752369 8748048181068150541314277)
  ·
    refine ⟨1640259033950278226496427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8748048181068150541314277 1640259033950278226496427)
    ·
      refine ⟨2460388550925417339744641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1640259033950278226496427 2460388550925417339744641)
      ·
        refine ⟨1845291413194063004808481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2460388550925417339744641 1845291413194063004808481)
        ·
          refine ⟨1383968559895547253606361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1845291413194063004808481 1383968559895547253606361)
          ·
            refine ⟨1037976419921660440204771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1383968559895547253606361 1037976419921660440204771)
            ·
              refine ⟨1556964629882490660307157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1037976419921660440204771 1556964629882490660307157)
              ·
                refine ⟨36491358512870874850949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1556964629882490660307157 36491358512870874850949)
                ·
                  rfl

theorem cell21_479700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 7].length) (baseStart_479700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_479700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_479700 prefixEnd_479700 := by exact prefixLift 479700
  have htrace : WordTrace (prefixWord ++ tailWord_479700) baseStart_479700 baseEnd_479700 := by
    simpa [prefixWord, tailWord_479700, baseEnd_479700] using wordTrace_append hprefix tailTrace_479700
  have hstable : (prefixWord ++ tailWord_479700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479700).length < 2 ^ (prefixWord ++ tailWord_479700).sum := by decide
  have hdescent : baseEnd_479700 < baseStart_479700 := by decide
  rcases family_descends (prefixWord ++ tailWord_479700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479717 : List Nat := [1, 3, 1, 5, 3, 1, 7]
def baseStart_479717 : Nat := 118140960795 + 479717 * 2 ^ 59
def prefixEnd_479717 : Nat := 4983230072969 + 3 ^ 40 * 479717 * 2
def baseEnd_479717 : Nat := 12164217241136041418831

theorem tailTrace_479717 : CollatzResearch.WordTrace tailWord_479717 prefixEnd_479717 12164217241136041418831 := by
  unfold tailWord_479717
  simp only [CollatzResearch.WordTrace]
  refine ⟨17496716403074712985997405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11664477602049808657331603 17496716403074712985997405)
  ·
    refine ⟨6561268651153017369749027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17496716403074712985997405 6561268651153017369749027)
    ·
      refine ⟨9841902976729526054623541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6561268651153017369749027 9841902976729526054623541)
      ·
        refine ⟨922678404068393067620957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9841902976729526054623541 922678404068393067620957)
        ·
          refine ⟨346004401525647400357859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 922678404068393067620957 346004401525647400357859)
          ·
            refine ⟨519006602288471100536789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346004401525647400357859 519006602288471100536789)
            ·
              refine ⟨12164217241136041418831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 519006602288471100536789 12164217241136041418831)
              ·
                rfl

theorem cell21_479717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 7].length) (baseStart_479717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_479717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_479717 prefixEnd_479717 := by exact prefixLift 479717
  have htrace : WordTrace (prefixWord ++ tailWord_479717) baseStart_479717 baseEnd_479717 := by
    simpa [prefixWord, tailWord_479717, baseEnd_479717] using wordTrace_append hprefix tailTrace_479717
  have hstable : (prefixWord ++ tailWord_479717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479717).length < 2 ^ (prefixWord ++ tailWord_479717).sum := by decide
  have hdescent : baseEnd_479717 < baseStart_479717 := by decide
  rcases family_descends (prefixWord ++ tailWord_479717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479728 : List Nat := [2, 1, 1, 1, 3, 3, 1, 3, 6]
def baseStart_479728 : Nat := 118140960795 + 479728 * 2 ^ 59
def prefixEnd_479728 : Nat := 4983230072969 + 3 ^ 40 * 479728 * 2
def baseEnd_479728 : Nat := 109480465520090798086123

theorem tailTrace_479728 : CollatzResearch.WordTrace tailWord_479728 prefixEnd_479728 109480465520090798086123 := by
  unfold tailWord_479728
  simp only [CollatzResearch.WordTrace]
  refine ⟨8748558803017430932323919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11664745070689907909765225 8748558803017430932323919)
  ·
    refine ⟨13122838204526146398485879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8748558803017430932323919 13122838204526146398485879)
    ·
      refine ⟨19684257306789219597728819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13122838204526146398485879 19684257306789219597728819)
      ·
        refine ⟨29526385960183829396593229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19684257306789219597728819 29526385960183829396593229)
        ·
          refine ⟨11072394735068936023722461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29526385960183829396593229 11072394735068936023722461)
          ·
            refine ⟨4152148025650851008895923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11072394735068936023722461 4152148025650851008895923)
            ·
              refine ⟨6228222038476276513343885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4152148025650851008895923 6228222038476276513343885)
              ·
                refine ⟨2335583264428603692503957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6228222038476276513343885 2335583264428603692503957)
                ·
                  refine ⟨109480465520090798086123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2335583264428603692503957 109480465520090798086123)
                  ·
                    rfl

theorem cell21_479728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 6].length) (baseStart_479728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_479728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_479728 prefixEnd_479728 := by exact prefixLift 479728
  have htrace : WordTrace (prefixWord ++ tailWord_479728) baseStart_479728 baseEnd_479728 := by
    simpa [prefixWord, tailWord_479728, baseEnd_479728] using wordTrace_append hprefix tailTrace_479728
  have hstable : (prefixWord ++ tailWord_479728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479728).length < 2 ^ (prefixWord ++ tailWord_479728).sum := by decide
  have hdescent : baseEnd_479728 < baseStart_479728 := by decide
  rcases family_descends (prefixWord ++ tailWord_479728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479776 : List Nat := [2, 1, 1, 6, 3, 8]
def baseStart_479776 : Nat := 118140960795 + 479776 * 2 ^ 59
def prefixEnd_479776 : Nat := 4983230072969 + 3 ^ 40 * 479776 * 2
def baseEnd_479776 : Nat := 4055237769409384492075

theorem tailTrace_479776 : CollatzResearch.WordTrace tailWord_479776 prefixEnd_479776 4055237769409384492075 := by
  unfold tailWord_479776
  simp only [CollatzResearch.WordTrace]
  refine ⟨8749434154930483031197591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11665912206573977374930121 8749434154930483031197591)
  ·
    refine ⟨13124151232395724546796387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8749434154930483031197591 13124151232395724546796387)
    ·
      refine ⟨19686226848593586820194581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13124151232395724546796387 19686226848593586820194581)
      ·
        refine ⟨922791883527824382196621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19686226848593586820194581 922791883527824382196621)
        ·
          refine ⟨346046956322934143323733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 922791883527824382196621 346046956322934143323733)
          ·
            refine ⟨4055237769409384492075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 346046956322934143323733 4055237769409384492075)
            ·
              rfl

theorem cell21_479776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 8].length) (baseStart_479776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_479776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_479776 prefixEnd_479776 := by exact prefixLift 479776
  have htrace : WordTrace (prefixWord ++ tailWord_479776) baseStart_479776 baseEnd_479776 := by
    simpa [prefixWord, tailWord_479776, baseEnd_479776] using wordTrace_append hprefix tailTrace_479776
  have hstable : (prefixWord ++ tailWord_479776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479776).length < 2 ^ (prefixWord ++ tailWord_479776).sum := by decide
  have hdescent : baseEnd_479776 < baseStart_479776 := by decide
  rcases family_descends (prefixWord ++ tailWord_479776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479869 : List Nat := [1, 4, 1, 1, 5, 2, 2, 5]
def baseStart_479869 : Nat := 118140960795 + 479869 * 2 ^ 59
def prefixEnd_479869 : Nat := 4983230072969 + 3 ^ 40 * 479869 * 2
def baseEnd_479869 : Nat := 36504214547035295411945

theorem tailTrace_479869 : CollatzResearch.WordTrace tailWord_479869 prefixEnd_479869 36504214547035295411945 := by
  unfold tailWord_479869
  simp only [CollatzResearch.WordTrace]
  refine ⟨17502260298524042945530661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11668173532349361963687107 17502260298524042945530661)
  ·
    refine ⟨3281673805973258052286999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17502260298524042945530661 3281673805973258052286999)
    ·
      refine ⟨4922510708959887078430499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3281673805973258052286999 4922510708959887078430499)
      ·
        refine ⟨7383766063439830617645749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4922510708959887078430499 7383766063439830617645749)
        ·
          refine ⟨692228068447484120404289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7383766063439830617645749 692228068447484120404289)
          ·
            refine ⟨519171051335613090303217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 692228068447484120404289 519171051335613090303217)
            ·
              refine ⟨389378288501709817727413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 519171051335613090303217 389378288501709817727413)
              ·
                refine ⟨36504214547035295411945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 389378288501709817727413 36504214547035295411945)
                ·
                  rfl

theorem cell21_479869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 5].length) (baseStart_479869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_479869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_479869 prefixEnd_479869 := by exact prefixLift 479869
  have htrace : WordTrace (prefixWord ++ tailWord_479869) baseStart_479869 baseEnd_479869 := by
    simpa [prefixWord, tailWord_479869, baseEnd_479869] using wordTrace_append hprefix tailTrace_479869
  have hstable : (prefixWord ++ tailWord_479869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479869).length < 2 ^ (prefixWord ++ tailWord_479869).sum := by decide
  have hdescent : baseEnd_479869 < baseStart_479869 := by decide
  rcases family_descends (prefixWord ++ tailWord_479869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479959 : List Nat := [1, 1, 3, 2, 1, 5, 1, 4, 3]
def baseStart_479959 : Nat := 118140960795 + 479959 * 2 ^ 59
def prefixEnd_479959 : Nat := 4983230072969 + 3 ^ 40 * 479959 * 2
def baseEnd_479959 : Nat := 109533182867285729735651

theorem tailTrace_479959 : CollatzResearch.WordTrace tailWord_479959 prefixEnd_479959 109533182867285729735651 := by
  unfold tailWord_479959
  simp only [CollatzResearch.WordTrace]
  refine ⟨17505542868197988316306931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11670361912131992210871287 17505542868197988316306931)
  ·
    refine ⟨26258314302296982474460397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17505542868197988316306931 26258314302296982474460397)
    ·
      refine ⟨9846867863361368427922649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26258314302296982474460397 9846867863361368427922649)
      ·
        refine ⟨7385150897521026320941987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9846867863361368427922649 7385150897521026320941987)
        ·
          refine ⟨11077726346281539481412981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7385150897521026320941987 11077726346281539481412981)
          ·
            refine ⟨1038536844963894326382467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11077726346281539481412981 1038536844963894326382467)
            ·
              refine ⟨1557805267445841489573701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1038536844963894326382467 1557805267445841489573701)
              ·
                refine ⟨292088487646095279295069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1557805267445841489573701 292088487646095279295069)
                ·
                  refine ⟨109533182867285729735651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 292088487646095279295069 109533182867285729735651)
                  ·
                    rfl

theorem cell21_479959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 4, 3].length) (baseStart_479959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_479959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_479959 prefixEnd_479959 := by exact prefixLift 479959
  have htrace : WordTrace (prefixWord ++ tailWord_479959) baseStart_479959 baseEnd_479959 := by
    simpa [prefixWord, tailWord_479959, baseEnd_479959] using wordTrace_append hprefix tailTrace_479959
  have hstable : (prefixWord ++ tailWord_479959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479959).length < 2 ^ (prefixWord ++ tailWord_479959).sum := by decide
  have hdescent : baseEnd_479959 < baseStart_479959 := by decide
  rcases family_descends (prefixWord ++ tailWord_479959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479973 : List Nat := [1, 3, 1, 4, 1, 2, 2, 3, 4]
def baseStart_479973 : Nat := 118140960795 + 479973 * 2 ^ 59
def prefixEnd_479973 : Nat := 4983230072969 + 3 ^ 40 * 479973 * 2
def baseEnd_479973 : Nat := 109536377858024816502289

theorem tailTrace_479973 : CollatzResearch.WordTrace tailWord_479973 prefixEnd_479973 109536377858024816502289 := by
  unfold tailWord_479973
  simp only [CollatzResearch.WordTrace]
  refine ⟨17506053490147268707316573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11670702326764845804877715 17506053490147268707316573)
  ·
    refine ⟨6564770058805225765243715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17506053490147268707316573 6564770058805225765243715)
    ·
      refine ⟨9847155088207838647865573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6564770058805225765243715 9847155088207838647865573)
      ·
        refine ⟨1846341579038969746474795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9847155088207838647865573 1846341579038969746474795)
        ·
          refine ⟨2769512368558454619712193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1846341579038969746474795 2769512368558454619712193)
          ·
            refine ⟨2077134276418840964784145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2769512368558454619712193 2077134276418840964784145)
            ·
              refine ⟨1557850707314130723588109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2077134276418840964784145 1557850707314130723588109)
              ·
                refine ⟨584194015242799021345541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1557850707314130723588109 584194015242799021345541)
                ·
                  refine ⟨109536377858024816502289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 584194015242799021345541 109536377858024816502289)
                  ·
                    rfl

theorem cell21_479973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_479973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_479973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_479973 prefixEnd_479973 := by exact prefixLift 479973
  have htrace : WordTrace (prefixWord ++ tailWord_479973) baseStart_479973 baseEnd_479973 := by
    simpa [prefixWord, tailWord_479973, baseEnd_479973] using wordTrace_append hprefix tailTrace_479973
  have hstable : (prefixWord ++ tailWord_479973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479973).length < 2 ^ (prefixWord ++ tailWord_479973).sum := by decide
  have hdescent : baseEnd_479973 < baseStart_479973 := by decide
  rcases family_descends (prefixWord ++ tailWord_479973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480001 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 9]
def baseStart_480001 : Nat := 118140960795 + 480001 * 2 ^ 59
def prefixEnd_480001 : Nat := 4983230072969 + 3 ^ 40 * 480001 * 2
def baseEnd_480001 : Nat := 109542767839502990035565

theorem tailTrace_480001 : CollatzResearch.WordTrace tailWord_480001 prefixEnd_480001 109542767839502990035565 := by
  unfold tailWord_480001
  simp only [CollatzResearch.WordTrace]
  refine ⟨17507074734045829489335857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11671383156030552992890571 17507074734045829489335857)
  ·
    refine ⟨13130306050534372117001893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17507074734045829489335857 13130306050534372117001893)
    ·
      refine ⟨2461932384475194771937855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13130306050534372117001893 2461932384475194771937855)
      ·
        refine ⟨3692898576712792157906783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2461932384475194771937855 3692898576712792157906783)
        ·
          refine ⟨5539347865069188236860175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3692898576712792157906783 5539347865069188236860175)
          ·
            refine ⟨8309021797603782355290263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5539347865069188236860175 8309021797603782355290263)
            ·
              refine ⟨12463532696405673532935395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8309021797603782355290263 12463532696405673532935395)
              ·
                refine ⟨18695299044608510299403093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12463532696405673532935395 18695299044608510299403093)
                ·
                  refine ⟨109542767839502990035565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18695299044608510299403093 109542767839502990035565)
                  ·
                    rfl

theorem cell21_480001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 9].length) (baseStart_480001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_480001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_480001 prefixEnd_480001 := by exact prefixLift 480001
  have htrace : WordTrace (prefixWord ++ tailWord_480001) baseStart_480001 baseEnd_480001 := by
    simpa [prefixWord, tailWord_480001, baseEnd_480001] using wordTrace_append hprefix tailTrace_480001
  have hstable : (prefixWord ++ tailWord_480001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480001).length < 2 ^ (prefixWord ++ tailWord_480001).sum := by decide
  have hdescent : baseEnd_480001 < baseStart_480001 := by decide
  rcases family_descends (prefixWord ++ tailWord_480001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480063 : List Nat := [1, 1, 2, 2, 5, 3, 7]
def baseStart_480063 : Nat := 118140960795 + 480063 * 2 ^ 59
def prefixEnd_480063 : Nat := 4983230072969 + 3 ^ 40 * 480063 * 2
def baseEnd_480063 : Nat := 12172990787133851111345

theorem tailTrace_480063 : CollatzResearch.WordTrace tailWord_480063 prefixEnd_480063 12172990787133851111345 := by
  unfold tailWord_480063
  simp only [CollatzResearch.WordTrace]
  refine ⟨17509336059821214078092843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11672890706547476052061895 17509336059821214078092843)
  ·
    refine ⟨26264004089731821117139265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17509336059821214078092843 26264004089731821117139265)
    ·
      refine ⟨19698003067298865837854449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26264004089731821117139265 19698003067298865837854449)
      ·
        refine ⟨14773502300474149378390837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19698003067298865837854449 14773502300474149378390837)
        ·
          refine ⟨1385015840669451504224141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14773502300474149378390837 1385015840669451504224141)
          ·
            refine ⟨519380940251044314084053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1385015840669451504224141 519380940251044314084053)
            ·
              refine ⟨12172990787133851111345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 519380940251044314084053 12172990787133851111345)
              ·
                rfl

theorem cell21_480063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 7].length) (baseStart_480063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_480063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_480063 prefixEnd_480063 := by exact prefixLift 480063
  have htrace : WordTrace (prefixWord ++ tailWord_480063) baseStart_480063 baseEnd_480063 := by
    simpa [prefixWord, tailWord_480063, baseEnd_480063] using wordTrace_append hprefix tailTrace_480063
  have hstable : (prefixWord ++ tailWord_480063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480063).length < 2 ^ (prefixWord ++ tailWord_480063).sum := by decide
  have hdescent : baseEnd_480063 < baseStart_480063 := by decide
  rcases family_descends (prefixWord ++ tailWord_480063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480184 : List Nat := [2, 1, 2, 1, 2, 5, 1, 1, 6]
def baseStart_480184 : Nat := 118140960795 + 480184 * 2 ^ 59
def prefixEnd_480184 : Nat := 4983230072969 + 3 ^ 40 * 480184 * 2
def baseEnd_480184 : Nat := 109584530932735338485191

theorem tailTrace_480184 : CollatzResearch.WordTrace tailWord_480184 prefixEnd_480184 109584530932735338485191 := by
  unfold tailWord_480184
  simp only [CollatzResearch.WordTrace]
  refine ⟨8756874646191425871623803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11675832861588567828831737 8756874646191425871623803)
  ·
    refine ⟨13135311969287138807435705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8756874646191425871623803 13135311969287138807435705)
    ·
      refine ⟨9851483976965354105576779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13135311969287138807435705 9851483976965354105576779)
      ·
        refine ⟨14777225965448031158365169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9851483976965354105576779 14777225965448031158365169)
        ·
          refine ⟨11082919474086023368773877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14777225965448031158365169 11082919474086023368773877)
          ·
            refine ⟨1039023700695564690822551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11082919474086023368773877 1039023700695564690822551)
            ·
              refine ⟨1558535551043347036233827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1039023700695564690822551 1558535551043347036233827)
              ·
                refine ⟨2337803326565020554350741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1558535551043347036233827 2337803326565020554350741)
                ·
                  refine ⟨109584530932735338485191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2337803326565020554350741 109584530932735338485191)
                  ·
                    rfl

theorem cell21_480184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 6].length) (baseStart_480184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_480184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_480184 prefixEnd_480184 := by exact prefixLift 480184
  have htrace : WordTrace (prefixWord ++ tailWord_480184) baseStart_480184 baseEnd_480184 := by
    simpa [prefixWord, tailWord_480184, baseEnd_480184] using wordTrace_append hprefix tailTrace_480184
  have hstable : (prefixWord ++ tailWord_480184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480184).length < 2 ^ (prefixWord ++ tailWord_480184).sum := by decide
  have hdescent : baseEnd_480184 < baseStart_480184 := by decide
  rcases family_descends (prefixWord ++ tailWord_480184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480305 : List Nat := [1, 2, 2, 3, 1, 2, 2, 3, 5]
def baseStart_480305 : Nat := 118140960795 + 480305 * 2 ^ 59
def prefixEnd_480305 : Nat := 4983230072969 + 3 ^ 40 * 480305 * 2
def baseEnd_480305 : Nat := 109612144781266016968277

theorem tailTrace_480305 : CollatzResearch.WordTrace tailWord_480305 prefixEnd_480305 109612144781266016968277 := by
  unfold tailWord_480305
  simp only [CollatzResearch.WordTrace]
  refine ⟨17518162524944489408402369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11678775016629659605601579 17518162524944489408402369)
  ·
    refine ⟨13138621893708367056301777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17518162524944489408402369 13138621893708367056301777)
    ·
      refine ⟨9853966420281275292226333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13138621893708367056301777 9853966420281275292226333)
      ·
        refine ⟨3695237407605478234584875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9853966420281275292226333 3695237407605478234584875)
        ·
          refine ⟨5542856111408217351877313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3695237407605478234584875 5542856111408217351877313)
          ·
            refine ⟨4157142083556163013907985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5542856111408217351877313 4157142083556163013907985)
            ·
              refine ⟨3117856562667122260430989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4157142083556163013907985 3117856562667122260430989)
              ·
                refine ⟨1169196211000170847661621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3117856562667122260430989 1169196211000170847661621)
                ·
                  refine ⟨109612144781266016968277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1169196211000170847661621 109612144781266016968277)
                  ·
                    rfl

theorem cell21_480305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 5].length) (baseStart_480305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_480305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_480305 prefixEnd_480305 := by exact prefixLift 480305
  have htrace : WordTrace (prefixWord ++ tailWord_480305) baseStart_480305 baseEnd_480305 := by
    simpa [prefixWord, tailWord_480305, baseEnd_480305] using wordTrace_append hprefix tailTrace_480305
  have hstable : (prefixWord ++ tailWord_480305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480305).length < 2 ^ (prefixWord ++ tailWord_480305).sum := by decide
  have hdescent : baseEnd_480305 < baseStart_480305 := by decide
  rcases family_descends (prefixWord ++ tailWord_480305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480308 : List Nat := [2, 5, 1, 2, 1, 1, 3, 6]
def baseStart_480308 : Nat := 118140960795 + 480308 * 2 ^ 59
def prefixEnd_480308 : Nat := 4983230072969 + 3 ^ 40 * 480308 * 2
def baseEnd_480308 : Nat := 36537609807379559472757

theorem tailTrace_480308 : CollatzResearch.WordTrace tailWord_480308 prefixEnd_480308 36537609807379559472757 := by
  unfold tailWord_480308
  simp only [CollatzResearch.WordTrace]
  refine ⟨8759135971966810460380789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11678847962622413947174385 8759135971966810460380789)
  ·
    refine ⟨821168997371888480660699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8759135971966810460380789 821168997371888480660699)
    ·
      refine ⟨1231753496057832720991049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 821168997371888480660699 1231753496057832720991049)
      ·
        refine ⟨923815122043374540743287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1231753496057832720991049 923815122043374540743287)
        ·
          refine ⟨1385722683065061811114931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 923815122043374540743287 1385722683065061811114931)
          ·
            refine ⟨2078584024597592716672397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1385722683065061811114931 2078584024597592716672397)
            ·
              refine ⟨779469009224097268752149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2078584024597592716672397 779469009224097268752149)
              ·
                refine ⟨36537609807379559472757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 779469009224097268752149 36537609807379559472757)
                ·
                  rfl

theorem cell21_480308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 6].length) (baseStart_480308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_480308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_480308 prefixEnd_480308 := by exact prefixLift 480308
  have htrace : WordTrace (prefixWord ++ tailWord_480308) baseStart_480308 baseEnd_480308 := by
    simpa [prefixWord, tailWord_480308, baseEnd_480308] using wordTrace_append hprefix tailTrace_480308
  have hstable : (prefixWord ++ tailWord_480308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480308).length < 2 ^ (prefixWord ++ tailWord_480308).sum := by decide
  have hdescent : baseEnd_480308 < baseStart_480308 := by decide
  rcases family_descends (prefixWord ++ tailWord_480308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480319 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 8]
def baseStart_480319 : Nat := 118140960795 + 480319 * 2 ^ 59
def prefixEnd_480319 : Nat := 4983230072969 + 3 ^ 40 * 480319 * 2
def baseEnd_480319 : Nat := 109615339772005103734915

theorem tailTrace_480319 : CollatzResearch.WordTrace tailWord_480319 prefixEnd_480319 109615339772005103734915 := by
  unfold tailWord_480319
  simp only [CollatzResearch.WordTrace]
  refine ⟨17518673146893769799412011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11679115431262513199608007 17518673146893769799412011)
  ·
    refine ⟨26278009720340654699118017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17518673146893769799412011 26278009720340654699118017)
    ·
      refine ⟨19708507290255491024338513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26278009720340654699118017 19708507290255491024338513)
      ·
        refine ⟨14781380467691618268253885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19708507290255491024338513 14781380467691618268253885)
        ·
          refine ⟨5543017675384356850595207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14781380467691618268253885 5543017675384356850595207)
          ·
            refine ⟨8314526513076535275892811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5543017675384356850595207 8314526513076535275892811)
            ·
              refine ⟨12471789769614802913839217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8314526513076535275892811 12471789769614802913839217)
              ·
                refine ⟨9353842327211102185379413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12471789769614802913839217 9353842327211102185379413)
                ·
                  refine ⟨109615339772005103734915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9353842327211102185379413 109615339772005103734915)
                  ·
                    rfl

theorem cell21_480319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 8].length) (baseStart_480319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_480319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_480319 prefixEnd_480319 := by exact prefixLift 480319
  have htrace : WordTrace (prefixWord ++ tailWord_480319) baseStart_480319 baseEnd_480319 := by
    simpa [prefixWord, tailWord_480319, baseEnd_480319] using wordTrace_append hprefix tailTrace_480319
  have hstable : (prefixWord ++ tailWord_480319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480319).length < 2 ^ (prefixWord ++ tailWord_480319).sum := by decide
  have hdescent : baseEnd_480319 < baseStart_480319 := by decide
  rcases family_descends (prefixWord ++ tailWord_480319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480381 : List Nat := [1, 4, 1, 1, 3, 1, 1, 4, 5]
def baseStart_480381 : Nat := 118140960795 + 480381 * 2 ^ 59
def prefixEnd_480381 : Nat := 4983230072969 + 3 ^ 40 * 480381 * 2
def baseEnd_480381 : Nat := 109629489016706773701455

theorem tailTrace_480381 : CollatzResearch.WordTrace tailWord_480381 prefixEnd_480381 109629489016706773701455 := by
  unfold tailWord_480381
  simp only [CollatzResearch.WordTrace]
  refine ⟨17520934472669154388168997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11680622981779436258779331 17520934472669154388168997)
  ·
    refine ⟨3285175213625466447781687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17520934472669154388168997 3285175213625466447781687)
    ·
      refine ⟨4927762820438199671672531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3285175213625466447781687 4927762820438199671672531)
      ·
        refine ⟨7391644230657299507508797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4927762820438199671672531 7391644230657299507508797)
        ·
          refine ⟨2771866586496487315315799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7391644230657299507508797 2771866586496487315315799)
          ·
            refine ⟨4157799879744730972973699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2771866586496487315315799 4157799879744730972973699)
            ·
              refine ⟨6236699819617096459460549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4157799879744730972973699 6236699819617096459460549)
              ·
                refine ⟨1169381216178205586148853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6236699819617096459460549 1169381216178205586148853)
                ·
                  refine ⟨109629489016706773701455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1169381216178205586148853 109629489016706773701455)
                  ·
                    rfl

theorem cell21_480381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_480381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_480381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_480381 prefixEnd_480381 := by exact prefixLift 480381
  have htrace : WordTrace (prefixWord ++ tailWord_480381) baseStart_480381 baseEnd_480381 := by
    simpa [prefixWord, tailWord_480381, baseEnd_480381] using wordTrace_append hprefix tailTrace_480381
  have hstable : (prefixWord ++ tailWord_480381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480381).length < 2 ^ (prefixWord ++ tailWord_480381).sum := by decide
  have hdescent : baseEnd_480381 < baseStart_480381 := by decide
  rcases family_descends (prefixWord ++ tailWord_480381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480412 : List Nat := [2, 2, 3, 2, 1, 2, 2, 1, 6]
def baseStart_480412 : Nat := 118140960795 + 480412 * 2 ^ 59
def prefixEnd_480412 : Nat := 4983230072969 + 3 ^ 40 * 480412 * 2
def baseEnd_480412 : Nat := 109636563639057608684725

theorem tailTrace_480412 : CollatzResearch.WordTrace tailWord_480412 prefixEnd_480412 109636563639057608684725 := by
  unfold tailWord_480412
  simp only [CollatzResearch.WordTrace]
  refine ⟨8761032567778423341273745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11681376757037897788364993 8761032567778423341273745)
  ·
    refine ⟨6570774425833817505955309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8761032567778423341273745 6570774425833817505955309)
    ·
      refine ⟨2464040409687681564733241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6570774425833817505955309 2464040409687681564733241)
      ·
        refine ⟨1848030307265761173549931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2464040409687681564733241 1848030307265761173549931)
        ·
          refine ⟨2772045460898641760324897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1848030307265761173549931 2772045460898641760324897)
          ·
            refine ⟨2079034095673981320243673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2772045460898641760324897 2079034095673981320243673)
            ·
              refine ⟨1559275571755485990182755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2079034095673981320243673 1559275571755485990182755)
              ·
                refine ⟨2338913357633228985274133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1559275571755485990182755 2338913357633228985274133)
                ·
                  refine ⟨109636563639057608684725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2338913357633228985274133 109636563639057608684725)
                  ·
                    rfl

theorem cell21_480412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_480412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_480412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_480412 prefixEnd_480412 := by exact prefixLift 480412
  have htrace : WordTrace (prefixWord ++ tailWord_480412) baseStart_480412 baseEnd_480412 := by
    simpa [prefixWord, tailWord_480412, baseEnd_480412] using wordTrace_append hprefix tailTrace_480412
  have hstable : (prefixWord ++ tailWord_480412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480412).length < 2 ^ (prefixWord ++ tailWord_480412).sum := by decide
  have hdescent : baseEnd_480412 < baseStart_480412 := by decide
  rcases family_descends (prefixWord ++ tailWord_480412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480415 : List Nat := [1, 1, 2, 6, 2, 2, 1, 1, 5]
def baseStart_480415 : Nat := 118140960795 + 480415 * 2 ^ 59
def prefixEnd_480415 : Nat := 4983230072969 + 3 ^ 40 * 480415 * 2
def baseEnd_480415 : Nat := 109637248279930270134719

theorem tailTrace_480415 : CollatzResearch.WordTrace tailWord_480415 prefixEnd_480415 109637248279930270134719 := by
  unfold tailWord_480415
  simp only [CollatzResearch.WordTrace]
  refine ⟨17522174554545978194906699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11681449703030652129937799 17522174554545978194906699)
  ·
    refine ⟨26283261831818967292360049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17522174554545978194906699 26283261831818967292360049)
    ·
      refine ⟨19712446373864225469270037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26283261831818967292360049 19712446373864225469270037)
      ·
        refine ⟨924020923774885568872033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19712446373864225469270037 924020923774885568872033)
        ·
          refine ⟨693015692831164176654025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 924020923774885568872033 693015692831164176654025)
          ·
            refine ⟨519761769623373132490519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 693015692831164176654025 519761769623373132490519)
            ·
              refine ⟨779642654435059698735779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519761769623373132490519 779642654435059698735779)
              ·
                refine ⟨1169463981652589548103669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 779642654435059698735779 1169463981652589548103669)
                ·
                  refine ⟨109637248279930270134719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1169463981652589548103669 109637248279930270134719)
                  ·
                    rfl

theorem cell21_480415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 5].length) (baseStart_480415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_480415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_480415 prefixEnd_480415 := by exact prefixLift 480415
  have htrace : WordTrace (prefixWord ++ tailWord_480415) baseStart_480415 baseEnd_480415 := by
    simpa [prefixWord, tailWord_480415, baseEnd_480415] using wordTrace_append hprefix tailTrace_480415
  have hstable : (prefixWord ++ tailWord_480415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480415).length < 2 ^ (prefixWord ++ tailWord_480415).sum := by decide
  have hdescent : baseEnd_480415 < baseStart_480415 := by decide
  rcases family_descends (prefixWord ++ tailWord_480415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480471 : List Nat := [1, 1, 3, 2, 1, 2, 2, 3, 6]
def baseStart_480471 : Nat := 118140960795 + 480471 * 2 ^ 59
def prefixEnd_480471 : Nat := 4983230072969 + 3 ^ 40 * 480471 * 2
def baseEnd_480471 : Nat := 109650028242886617201271

theorem tailTrace_480471 : CollatzResearch.WordTrace tailWord_480471 prefixEnd_480471 109650028242886617201271 := by
  unfold tailWord_480471
  simp only [CollatzResearch.WordTrace]
  refine ⟨17524217042343099758945267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11682811361562066505963511 17524217042343099758945267)
  ·
    refine ⟨26286325563514649638417901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17524217042343099758945267 26286325563514649638417901)
    ·
      refine ⟨9857372086317993614406713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26286325563514649638417901 9857372086317993614406713)
      ·
        refine ⟨7393029064738495210805035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9857372086317993614406713 7393029064738495210805035)
        ·
          refine ⟨11089543597107742816207553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7393029064738495210805035 11089543597107742816207553)
          ·
            refine ⟨8317157697830807112155665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11089543597107742816207553 8317157697830807112155665)
            ·
              refine ⟨6237868273373105334116749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8317157697830807112155665 6237868273373105334116749)
              ·
                refine ⟨2339200602514914500293781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6237868273373105334116749 2339200602514914500293781)
                ·
                  refine ⟨109650028242886617201271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2339200602514914500293781 109650028242886617201271)
                  ·
                    rfl

theorem cell21_480471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 6].length) (baseStart_480471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_480471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_480471 prefixEnd_480471 := by exact prefixLift 480471
  have htrace : WordTrace (prefixWord ++ tailWord_480471) baseStart_480471 baseEnd_480471 := by
    simpa [prefixWord, tailWord_480471, baseEnd_480471] using wordTrace_append hprefix tailTrace_480471
  have hstable : (prefixWord ++ tailWord_480471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480471).length < 2 ^ (prefixWord ++ tailWord_480471).sum := by decide
  have hdescent : baseEnd_480471 < baseStart_480471 := by decide
  rcases family_descends (prefixWord ++ tailWord_480471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480477 : List Nat := [1, 4, 3, 2, 3, 1, 1, 6]
def baseStart_480477 : Nat := 118140960795 + 480477 * 2 ^ 59
def prefixEnd_480477 : Nat := 4983230072969 + 3 ^ 40 * 480477 * 2
def baseEnd_480477 : Nat := 36550465841543980033753

theorem tailTrace_480477 : CollatzResearch.WordTrace tailWord_480477 prefixEnd_480477 36550465841543980033753 := by
  unfold tailWord_480477
  simp only [CollatzResearch.WordTrace]
  refine ⟨17524435880321362783663685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11682957253547575189109123 17524435880321362783663685)
  ·
    refine ⟨3285831727560255521936941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17524435880321362783663685 3285831727560255521936941)
    ·
      refine ⟨1232186897835095820726353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3285831727560255521936941 1232186897835095820726353)
      ·
        refine ⟨924140173376321865544765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1232186897835095820726353 924140173376321865544765)
        ·
          refine ⟨346552565016120699579287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 924140173376321865544765 346552565016120699579287)
          ·
            refine ⟨519828847524181049368931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346552565016120699579287 519828847524181049368931)
            ·
              refine ⟨779743271286271574053397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519828847524181049368931 779743271286271574053397)
              ·
                refine ⟨36550465841543980033753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 779743271286271574053397 36550465841543980033753)
                ·
                  rfl

theorem cell21_480477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 6].length) (baseStart_480477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_480477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_480477 prefixEnd_480477 := by exact prefixLift 480477
  have htrace : WordTrace (prefixWord ++ tailWord_480477) baseStart_480477 baseEnd_480477 := by
    simpa [prefixWord, tailWord_480477, baseEnd_480477] using wordTrace_append hprefix tailTrace_480477
  have hstable : (prefixWord ++ tailWord_480477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480477).length < 2 ^ (prefixWord ++ tailWord_480477).sum := by decide
  have hdescent : baseEnd_480477 < baseStart_480477 := by decide
  rcases family_descends (prefixWord ++ tailWord_480477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480488 : List Nat := [2, 1, 4, 1, 2, 1, 1, 5, 4]
def baseStart_480488 : Nat := 118140960795 + 480488 * 2 ^ 59
def prefixEnd_480488 : Nat := 4983230072969 + 3 ^ 40 * 480488 * 2
def baseEnd_480488 : Nat := 109653907874498365417903

theorem tailTrace_480488 : CollatzResearch.WordTrace tailWord_480488 prefixEnd_480488 109653907874498365417903 := by
  unfold tailWord_480488
  simp only [CollatzResearch.WordTrace]
  refine ⟨8762418541640755831157059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11683224722187674441542745 8762418541640755831157059)
  ·
    refine ⟨13143627812461133746735589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8762418541640755831157059 13143627812461133746735589)
    ·
      refine ⟨2464430214836462577512923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13143627812461133746735589 2464430214836462577512923)
      ·
        refine ⟨3696645322254693866269385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2464430214836462577512923 3696645322254693866269385)
        ·
          refine ⟨2772483991691020399702039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3696645322254693866269385 2772483991691020399702039)
          ·
            refine ⟨4158725987536530599553059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2772483991691020399702039 4158725987536530599553059)
            ·
              refine ⟨6238088981304795899329589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4158725987536530599553059 6238088981304795899329589)
              ·
                refine ⟨584820841997324615562149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6238088981304795899329589 584820841997324615562149)
                ·
                  refine ⟨109653907874498365417903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 584820841997324615562149 109653907874498365417903)
                  ·
                    rfl

theorem cell21_480488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 4].length) (baseStart_480488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_480488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_480488 prefixEnd_480488 := by exact prefixLift 480488
  have htrace : WordTrace (prefixWord ++ tailWord_480488) baseStart_480488 baseEnd_480488 := by
    simpa [prefixWord, tailWord_480488, baseEnd_480488] using wordTrace_append hprefix tailTrace_480488
  have hstable : (prefixWord ++ tailWord_480488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480488).length < 2 ^ (prefixWord ++ tailWord_480488).sum := by decide
  have hdescent : baseEnd_480488 < baseStart_480488 := by decide
  rcases family_descends (prefixWord ++ tailWord_480488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480564 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 8]
def baseStart_480564 : Nat := 118140960795 + 480564 * 2 ^ 59
def prefixEnd_480564 : Nat := 4983230072969 + 3 ^ 40 * 480564 * 2
def baseEnd_480564 : Nat := 109671252109939122151081

theorem tailTrace_480564 : CollatzResearch.WordTrace tailWord_480564 prefixEnd_480564 109671252109939122151081 := by
  unfold tailWord_480564
  simp only [CollatzResearch.WordTrace]
  refine ⟨8763804515503088321040373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11685072687337451094720497 8763804515503088321040373)
  ·
    refine ⟨821606673328414530097535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8763804515503088321040373 821606673328414530097535)
    ·
      refine ⟨1232410009992621795146303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 821606673328414530097535 1232410009992621795146303)
      ·
        refine ⟨1848615014988932692719455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1232410009992621795146303 1848615014988932692719455)
        ·
          refine ⟨2772922522483399039079183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1848615014988932692719455 2772922522483399039079183)
          ·
            refine ⟨4159383783725098558618775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2772922522483399039079183 4159383783725098558618775)
            ·
              refine ⟨6239075675587647837928163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4159383783725098558618775 6239075675587647837928163)
              ·
                refine ⟨9358613513381471756892245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6239075675587647837928163 9358613513381471756892245)
                ·
                  refine ⟨109671252109939122151081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9358613513381471756892245 109671252109939122151081)
                  ·
                    rfl

theorem cell21_480564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_480564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_480564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_480564 prefixEnd_480564 := by exact prefixLift 480564
  have htrace : WordTrace (prefixWord ++ tailWord_480564) baseStart_480564 baseEnd_480564 := by
    simpa [prefixWord, tailWord_480564, baseEnd_480564] using wordTrace_append hprefix tailTrace_480564
  have hstable : (prefixWord ++ tailWord_480564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480564).length < 2 ^ (prefixWord ++ tailWord_480564).sum := by decide
  have hdescent : baseEnd_480564 < baseStart_480564 := by decide
  rcases family_descends (prefixWord ++ tailWord_480564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480626 : List Nat := [3, 2, 1, 2, 1, 2, 2, 5, 3]
def baseStart_480626 : Nat := 118140960795 + 480626 * 2 ^ 59
def prefixEnd_480626 : Nat := 4983230072969 + 3 ^ 40 * 480626 * 2
def baseEnd_480626 : Nat := 109685401354640792117621

theorem tailTrace_480626 : CollatzResearch.WordTrace tailWord_480626 prefixEnd_480626 109685401354640792117621 := by
  unfold tailWord_480626
  simp only [CollatzResearch.WordTrace]
  refine ⟨4382467589195390307709433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11686580237854374153891821 4382467589195390307709433)
  ·
    refine ⟨3286850691896542730782075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4382467589195390307709433 3286850691896542730782075)
    ·
      refine ⟨4930276037844814096173113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3286850691896542730782075 4930276037844814096173113)
      ·
        refine ⟨3697707028383610572129835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4930276037844814096173113 3697707028383610572129835)
        ·
          refine ⟨5546560542575415858194753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3697707028383610572129835 5546560542575415858194753)
          ·
            refine ⟨4159920406931561893646065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5546560542575415858194753 4159920406931561893646065)
            ·
              refine ⟨3119940305198671420234549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4159920406931561893646065 3119940305198671420234549)
              ·
                refine ⟨292494403612375445646989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3119940305198671420234549 292494403612375445646989)
                ·
                  refine ⟨109685401354640792117621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 292494403612375445646989 109685401354640792117621)
                  ·
                    rfl

theorem cell21_480626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_480626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_480626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_480626 prefixEnd_480626 := by exact prefixLift 480626
  have htrace : WordTrace (prefixWord ++ tailWord_480626) baseStart_480626 baseEnd_480626 := by
    simpa [prefixWord, tailWord_480626, baseEnd_480626] using wordTrace_append hprefix tailTrace_480626
  have hstable : (prefixWord ++ tailWord_480626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480626).length < 2 ^ (prefixWord ++ tailWord_480626).sum := by decide
  have hdescent : baseEnd_480626 < baseStart_480626 := by decide
  rcases family_descends (prefixWord ++ tailWord_480626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480643 : List Nat := [1, 1, 1, 3, 5, 1, 4, 2, 3]
def baseStart_480643 : Nat := 118140960795 + 480643 * 2 ^ 59
def prefixEnd_480643 : Nat := 4983230072969 + 3 ^ 40 * 480643 * 2
def baseEnd_480643 : Nat := 109689280986252540334253

theorem tailTrace_480643 : CollatzResearch.WordTrace tailWord_480643 prefixEnd_480643 109689280986252540334253 := by
  unfold tailWord_480643
  simp only [CollatzResearch.WordTrace]
  refine ⟨17530490397719973134206583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11686993598479982089471055 17530490397719973134206583)
  ·
    refine ⟨26295735596579959701309875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17530490397719973134206583 26295735596579959701309875)
    ·
      refine ⟨39443603394869939551964813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26295735596579959701309875 39443603394869939551964813)
      ·
        refine ⟨14791351273076227331986805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39443603394869939551964813 14791351273076227331986805)
        ·
          refine ⟨1386689181850896312373763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14791351273076227331986805 1386689181850896312373763)
          ·
            refine ⟨2080033772776344468560645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386689181850896312373763 2080033772776344468560645)
            ·
              refine ⟨390006332395564587855121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2080033772776344468560645 390006332395564587855121)
              ·
                refine ⟨292504749296673440891341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 390006332395564587855121 292504749296673440891341)
                ·
                  refine ⟨109689280986252540334253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 292504749296673440891341 109689280986252540334253)
                  ·
                    rfl

theorem cell21_480643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 2, 3].length) (baseStart_480643 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_480643 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_480643 prefixEnd_480643 := by exact prefixLift 480643
  have htrace : WordTrace (prefixWord ++ tailWord_480643) baseStart_480643 baseEnd_480643 := by
    simpa [prefixWord, tailWord_480643, baseEnd_480643] using wordTrace_append hprefix tailTrace_480643
  have hstable : (prefixWord ++ tailWord_480643).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480643).length < 2 ^ (prefixWord ++ tailWord_480643).sum := by decide
  have hdescent : baseEnd_480643 < baseStart_480643 := by decide
  rcases family_descends (prefixWord ++ tailWord_480643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480671 : List Nat := [1, 1, 2, 5, 1, 3, 3, 5]
def baseStart_480671 : Nat := 118140960795 + 480671 * 2 ^ 59
def prefixEnd_480671 : Nat := 4983230072969 + 3 ^ 40 * 480671 * 2
def baseEnd_480671 : Nat := 36565223655910237955843

theorem tailTrace_480671 : CollatzResearch.WordTrace tailWord_480671 prefixEnd_480671 36565223655910237955843 := by
  unfold tailWord_480671
  simp only [CollatzResearch.WordTrace]
  refine ⟨17531511641618533916225867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11687674427745689277483911 17531511641618533916225867)
  ·
    refine ⟨26297267462427800874338801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17531511641618533916225867 26297267462427800874338801)
    ·
      refine ⟨19722950596820850655754101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26297267462427800874338801 19722950596820850655754101)
      ·
        refine ⟨1849026618451954748976947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19722950596820850655754101 1849026618451954748976947)
        ·
          refine ⟨2773539927677932123465421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1849026618451954748976947 2773539927677932123465421)
          ·
            refine ⟨1040077472879224546299533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2773539927677932123465421 1040077472879224546299533)
            ·
              refine ⟨390029052329709204862325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1040077472879224546299533 390029052329709204862325)
              ·
                refine ⟨36565223655910237955843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 390029052329709204862325 36565223655910237955843)
                ·
                  rfl

theorem cell21_480671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 5].length) (baseStart_480671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_480671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_480671 prefixEnd_480671 := by exact prefixLift 480671
  have htrace : WordTrace (prefixWord ++ tailWord_480671) baseStart_480671 baseEnd_480671 := by
    simpa [prefixWord, tailWord_480671, baseEnd_480671] using wordTrace_append hprefix tailTrace_480671
  have hstable : (prefixWord ++ tailWord_480671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480671).length < 2 ^ (prefixWord ++ tailWord_480671).sum := by decide
  have hdescent : baseEnd_480671 < baseStart_480671 := by decide
  rcases family_descends (prefixWord ++ tailWord_480671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480713 : List Nat := [1, 2, 1, 1, 2, 1, 3, 10]
def baseStart_480713 : Nat := 118140960795 + 480713 * 2 ^ 59
def prefixEnd_480713 : Nat := 4983230072969 + 3 ^ 40 * 480713 * 2
def baseEnd_480713 : Nat := 36568418646649324722481

theorem tailTrace_480713 : CollatzResearch.WordTrace tailWord_480713 prefixEnd_480713 36568418646649324722481 := by
  unfold tailWord_480713
  simp only [CollatzResearch.WordTrace]
  refine ⟨17533043507466375089254793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11688695671644250059503195 17533043507466375089254793)
  ·
    refine ⟨13149782630599781316941095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17533043507466375089254793 13149782630599781316941095)
    ·
      refine ⟨19724673945899671975411643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13149782630599781316941095 19724673945899671975411643)
      ·
        refine ⟨29587010918849507963117465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19724673945899671975411643 29587010918849507963117465)
        ·
          refine ⟨22190258189137130972338099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29587010918849507963117465 22190258189137130972338099)
          ·
            refine ⟨33285387283705696458507149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22190258189137130972338099 33285387283705696458507149)
            ·
              refine ⟨12482020231389636171940181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33285387283705696458507149 12482020231389636171940181)
              ·
                refine ⟨36568418646649324722481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12482020231389636171940181 36568418646649324722481)
                ·
                  rfl

theorem cell21_480713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 10].length) (baseStart_480713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_480713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_480713 prefixEnd_480713 := by exact prefixLift 480713
  have htrace : WordTrace (prefixWord ++ tailWord_480713) baseStart_480713 baseEnd_480713 := by
    simpa [prefixWord, tailWord_480713, baseEnd_480713] using wordTrace_append hprefix tailTrace_480713
  have hstable : (prefixWord ++ tailWord_480713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480713).length < 2 ^ (prefixWord ++ tailWord_480713).sum := by decide
  have hdescent : baseEnd_480713 < baseStart_480713 := by decide
  rcases family_descends (prefixWord ++ tailWord_480713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480730 : List Nat := [3, 1, 1, 2, 3, 3, 1, 7]
def baseStart_480730 : Nat := 118140960795 + 480730 * 2 ^ 59
def prefixEnd_480730 : Nat := 4983230072969 + 3 ^ 40 * 480730 * 2
def baseEnd_480730 : Nat := 36569711857186574128025

theorem tailTrace_480730 : CollatzResearch.WordTrace tailWord_480730 prefixEnd_480730 36569711857186574128025 := by
  unfold tailWord_480730
  simp only [CollatzResearch.WordTrace]
  refine ⟨4383415887101196748155911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11689109032269857995082429 4383415887101196748155911)
  ·
    refine ⟨6575123830651795122233867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4383415887101196748155911 6575123830651795122233867)
    ·
      refine ⟨9862685745977692683350801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6575123830651795122233867 9862685745977692683350801)
      ·
        refine ⟨7397014309483269512513101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9862685745977692683350801 7397014309483269512513101)
        ·
          refine ⟨2773880366056226067192413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7397014309483269512513101 2773880366056226067192413)
          ·
            refine ⟨1040205137271084775197155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2773880366056226067192413 1040205137271084775197155)
            ·
              refine ⟨1560307705906627162795733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1040205137271084775197155 1560307705906627162795733)
              ·
                refine ⟨36569711857186574128025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1560307705906627162795733 36569711857186574128025)
                ·
                  rfl

theorem cell21_480730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 7].length) (baseStart_480730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_480730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_480730 prefixEnd_480730 := by exact prefixLift 480730
  have htrace : WordTrace (prefixWord ++ tailWord_480730) baseStart_480730 baseEnd_480730 := by
    simpa [prefixWord, tailWord_480730, baseEnd_480730] using wordTrace_append hprefix tailTrace_480730
  have hstable : (prefixWord ++ tailWord_480730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480730).length < 2 ^ (prefixWord ++ tailWord_480730).sum := by decide
  have hdescent : baseEnd_480730 < baseStart_480730 := by decide
  rcases family_descends (prefixWord ++ tailWord_480730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480865 : List Nat := [1, 2, 3, 1, 1, 3, 10]
def baseStart_480865 : Nat := 118140960795 + 480865 * 2 ^ 59
def prefixEnd_480865 : Nat := 4983230072969 + 3 ^ 40 * 480865 * 2
def baseEnd_480865 : Nat := 12193327156758831959311

theorem tailTrace_480865 : CollatzResearch.WordTrace tailWord_480865 prefixEnd_480865 12193327156758831959311 := by
  unfold tailWord_480865
  simp only [CollatzResearch.WordTrace]
  refine ⟨17538587402915705048788049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11692391601943803365858699 17538587402915705048788049)
  ·
    refine ⟨13153940552186778786591037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17538587402915705048788049 13153940552186778786591037)
    ·
      refine ⟨4932727707070042044971639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13153940552186778786591037 4932727707070042044971639)
      ·
        refine ⟨7399091560605063067457459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4932727707070042044971639 7399091560605063067457459)
        ·
          refine ⟨11098637340907594601186189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7399091560605063067457459 11098637340907594601186189)
          ·
            refine ⟨4161989002840347975444821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11098637340907594601186189 4161989002840347975444821)
            ·
              refine ⟨12193327156758831959311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4161989002840347975444821 12193327156758831959311)
              ·
                rfl

theorem cell21_480865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 10].length) (baseStart_480865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_480865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_480865 prefixEnd_480865 := by exact prefixLift 480865
  have htrace : WordTrace (prefixWord ++ tailWord_480865) baseStart_480865 baseEnd_480865 := by
    simpa [prefixWord, tailWord_480865, baseEnd_480865] using wordTrace_append hprefix tailTrace_480865
  have hstable : (prefixWord ++ tailWord_480865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480865).length < 2 ^ (prefixWord ++ tailWord_480865).sum := by decide
  have hdescent : baseEnd_480865 < baseStart_480865 := by decide
  rcases family_descends (prefixWord ++ tailWord_480865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480868 : List Nat := [2, 3, 1, 1, 2, 3, 3, 2, 4]
def baseStart_480868 : Nat := 118140960795 + 480868 * 2 ^ 59
def prefixEnd_480868 : Nat := 4983230072969 + 3 ^ 40 * 480868 * 2
def baseEnd_480868 : Nat := 109740629051702149083793

theorem tailTrace_480868 : CollatzResearch.WordTrace tailWord_480868 prefixEnd_480868 109740629051702149083793 := by
  unfold tailWord_480868
  simp only [CollatzResearch.WordTrace]
  refine ⟨8769348410952418280573629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11692464547936557707431505 8769348410952418280573629)
  ·
    refine ⟨3288505654107156855215111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8769348410952418280573629 3288505654107156855215111)
    ·
      refine ⟨4932758481160735282822667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3288505654107156855215111 4932758481160735282822667)
      ·
        refine ⟨7399137721741102924234001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4932758481160735282822667 7399137721741102924234001)
        ·
          refine ⟨5549353291305827193175501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7399137721741102924234001 5549353291305827193175501)
          ·
            refine ⟨2081007484239685197440813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5549353291305827193175501 2081007484239685197440813)
            ·
              refine ⟨780377806589881949040305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2081007484239685197440813 780377806589881949040305)
              ·
                refine ⟨585283354942411461780229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 780377806589881949040305 585283354942411461780229)
                ·
                  refine ⟨109740629051702149083793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 585283354942411461780229 109740629051702149083793)
                  ·
                    rfl

theorem cell21_480868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_480868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_480868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_480868 prefixEnd_480868 := by exact prefixLift 480868
  have htrace : WordTrace (prefixWord ++ tailWord_480868) baseStart_480868 baseEnd_480868 := by
    simpa [prefixWord, tailWord_480868, baseEnd_480868] using wordTrace_append hprefix tailTrace_480868
  have hstable : (prefixWord ++ tailWord_480868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480868).length < 2 ^ (prefixWord ++ tailWord_480868).sum := by decide
  have hdescent : baseEnd_480868 < baseStart_480868 := by decide
  rcases family_descends (prefixWord ++ tailWord_480868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480896 : List Nat := [2, 1, 1, 2, 1, 4, 1, 4, 5]
def baseStart_480896 : Nat := 118140960795 + 480896 * 2 ^ 59
def prefixEnd_480896 : Nat := 4983230072969 + 3 ^ 40 * 480896 * 2
def baseEnd_480896 : Nat := 109747019033180322617069

theorem tailTrace_480896 : CollatzResearch.WordTrace tailWord_480896 prefixEnd_480896 109747019033180322617069 := by
  unfold tailWord_480896
  simp only [CollatzResearch.WordTrace]
  refine ⟨8769859032901698671583271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11693145377202264895444361 8769859032901698671583271)
  ·
    refine ⟨13154788549352548007374907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8769859032901698671583271 13154788549352548007374907)
    ·
      refine ⟨19732182824028822011062361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13154788549352548007374907 19732182824028822011062361)
      ·
        refine ⟨14799137118021616508296771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19732182824028822011062361 14799137118021616508296771)
        ·
          refine ⟨22198705677032424762445157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14799137118021616508296771 22198705677032424762445157)
          ·
            refine ⟨4162257314443579642958467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22198705677032424762445157 4162257314443579642958467)
            ·
              refine ⟨6243385971665369464437701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4162257314443579642958467 6243385971665369464437701)
              ·
                refine ⟨1170634869687256774582069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6243385971665369464437701 1170634869687256774582069)
                ·
                  refine ⟨109747019033180322617069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1170634869687256774582069 109747019033180322617069)
                  ·
                    rfl

theorem cell21_480896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 5].length) (baseStart_480896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_480896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_480896 prefixEnd_480896 := by exact prefixLift 480896
  have htrace : WordTrace (prefixWord ++ tailWord_480896) baseStart_480896 baseEnd_480896 := by
    simpa [prefixWord, tailWord_480896, baseEnd_480896] using wordTrace_append hprefix tailTrace_480896
  have hstable : (prefixWord ++ tailWord_480896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480896).length < 2 ^ (prefixWord ++ tailWord_480896).sum := by decide
  have hdescent : baseEnd_480896 < baseStart_480896 := by decide
  rcases family_descends (prefixWord ++ tailWord_480896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480913 : List Nat := [1, 2, 2, 1, 1, 1, 1, 9, 3]
def baseStart_480913 : Nat := 118140960795 + 480913 * 2 ^ 59
def prefixEnd_480913 : Nat := 4983230072969 + 3 ^ 40 * 480913 * 2
def baseEnd_480913 : Nat := 109750898664792070833701

theorem tailTrace_480913 : CollatzResearch.WordTrace tailWord_480913 prefixEnd_480913 109750898664792070833701 := by
  unfold tailWord_480913
  simp only [CollatzResearch.WordTrace]
  refine ⟨17540338106741809246535393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11693558737827872831023595 17540338106741809246535393)
  ·
    refine ⟨13155253580056356934901545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17540338106741809246535393 13155253580056356934901545)
    ·
      refine ⟨9866440185042267701176159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13155253580056356934901545 9866440185042267701176159)
      ·
        refine ⟨14799660277563401551764239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9866440185042267701176159 14799660277563401551764239)
        ·
          refine ⟨22199490416345102327646359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14799660277563401551764239 22199490416345102327646359)
          ·
            refine ⟨33299235624517653491469539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22199490416345102327646359 33299235624517653491469539)
            ·
              refine ⟨49948853436776480237204309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33299235624517653491469539 49948853436776480237204309)
              ·
                refine ⟨292669063106112188889869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 49948853436776480237204309 292669063106112188889869)
                ·
                  refine ⟨109750898664792070833701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 292669063106112188889869 109750898664792070833701)
                  ·
                    rfl

theorem cell21_480913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 9, 3].length) (baseStart_480913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_480913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_480913 prefixEnd_480913 := by exact prefixLift 480913
  have htrace : WordTrace (prefixWord ++ tailWord_480913) baseStart_480913 baseEnd_480913 := by
    simpa [prefixWord, tailWord_480913, baseEnd_480913] using wordTrace_append hprefix tailTrace_480913
  have hstable : (prefixWord ++ tailWord_480913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480913).length < 2 ^ (prefixWord ++ tailWord_480913).sum := by decide
  have hdescent : baseEnd_480913 < baseStart_480913 := by decide
  rcases family_descends (prefixWord ++ tailWord_480913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480916 : List Nat := [2, 4, 2, 2, 3, 1, 7]
def baseStart_480916 : Nat := 118140960795 + 480916 * 2 ^ 59
def prefixEnd_480916 : Nat := 4983230072969 + 3 ^ 40 * 480916 * 2
def baseEnd_480916 : Nat := 12194620367296081364855

theorem tailTrace_480916 : CollatzResearch.WordTrace tailWord_480916 prefixEnd_480916 12194620367296081364855 := by
  unfold tailWord_480916
  simp only [CollatzResearch.WordTrace]
  refine ⟨8770223762865470379447301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11693631683820627172596401 8770223762865470379447301)
  ·
    refine ⟨1644416955537275696146369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8770223762865470379447301 1644416955537275696146369)
    ·
      refine ⟨1233312716652956772109777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1644416955537275696146369 1233312716652956772109777)
      ·
        refine ⟨924984537489717579082333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1233312716652956772109777 924984537489717579082333)
        ·
          refine ⟨346869201558644092155875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 924984537489717579082333 346869201558644092155875)
          ·
            refine ⟨520303802337966138233813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346869201558644092155875 520303802337966138233813)
            ·
              refine ⟨12194620367296081364855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 520303802337966138233813 12194620367296081364855)
              ·
                rfl

theorem cell21_480916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 7].length) (baseStart_480916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_480916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_480916 prefixEnd_480916 := by exact prefixLift 480916
  have htrace : WordTrace (prefixWord ++ tailWord_480916) baseStart_480916 baseEnd_480916 := by
    simpa [prefixWord, tailWord_480916, baseEnd_480916] using wordTrace_append hprefix tailTrace_480916
  have hstable : (prefixWord ++ tailWord_480916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480916).length < 2 ^ (prefixWord ++ tailWord_480916).sum := by decide
  have hdescent : baseEnd_480916 < baseStart_480916 := by decide
  rcases family_descends (prefixWord ++ tailWord_480916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480936 : List Nat := [2, 1, 7, 1, 1, 2, 2, 1, 4]
def baseStart_480936 : Nat := 118140960795 + 480936 * 2 ^ 59
def prefixEnd_480936 : Nat := 4983230072969 + 3 ^ 40 * 480936 * 2
def baseEnd_480936 : Nat := 109756147578149141950321

theorem tailTrace_480936 : CollatzResearch.WordTrace tailWord_480936 prefixEnd_480936 109756147578149141950321 := by
  unfold tailWord_480936
  simp only [CollatzResearch.WordTrace]
  refine ⟨8770588492829242087311331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11694117990438989449748441 8770588492829242087311331)
  ·
    refine ⟨13155882739243863130966997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8770588492829242087311331 13155882739243863130966997)
    ·
      refine ⟨308341001701028042132039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 13155882739243863130966997 308341001701028042132039)
      ·
        refine ⟨462511502551542063198059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308341001701028042132039 462511502551542063198059)
        ·
          refine ⟨693767253827313094797089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462511502551542063198059 693767253827313094797089)
          ·
            refine ⟨520325440370484821097817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 693767253827313094797089 520325440370484821097817)
            ·
              refine ⟨390244080277863615823363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 520325440370484821097817 390244080277863615823363)
              ·
                refine ⟨585366120416795423735045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390244080277863615823363 585366120416795423735045)
                ·
                  refine ⟨109756147578149141950321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 585366120416795423735045 109756147578149141950321)
                  ·
                    rfl

theorem cell21_480936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 4].length) (baseStart_480936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_480936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_480936 prefixEnd_480936 := by exact prefixLift 480936
  have htrace : WordTrace (prefixWord ++ tailWord_480936) baseStart_480936 baseEnd_480936 := by
    simpa [prefixWord, tailWord_480936, baseEnd_480936] using wordTrace_append hprefix tailTrace_480936
  have hstable : (prefixWord ++ tailWord_480936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480936).length < 2 ^ (prefixWord ++ tailWord_480936).sum := by decide
  have hdescent : baseEnd_480936 < baseStart_480936 := by decide
  rcases family_descends (prefixWord ++ tailWord_480936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480944 : List Nat := [2, 1, 1, 1, 2, 1, 8, 1, 4]
def baseStart_480944 : Nat := 118140960795 + 480944 * 2 ^ 59
def prefixEnd_480944 : Nat := 4983230072969 + 3 ^ 40 * 480944 * 2
def baseEnd_480944 : Nat := 109757973287142905816971

theorem tailTrace_480944 : CollatzResearch.WordTrace tailWord_480944 prefixEnd_480944 109757973287142905816971 := by
  unfold tailWord_480944
  simp only [CollatzResearch.WordTrace]
  refine ⟨8770734384814750770456943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11694312513086334360609257 8770734384814750770456943)
  ·
    refine ⟨13156101577222126155685415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8770734384814750770456943 13156101577222126155685415)
    ·
      refine ⟨19734152365833189233528123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13156101577222126155685415 19734152365833189233528123)
      ·
        refine ⟨29601228548749783850292185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19734152365833189233528123 29601228548749783850292185)
        ·
          refine ⟨22200921411562337887719139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29601228548749783850292185 22200921411562337887719139)
          ·
            refine ⟨33301382117343506831578709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22200921411562337887719139 33301382117343506831578709)
            ·
              refine ⟨390250571687619220682563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 33301382117343506831578709 390250571687619220682563)
              ·
                refine ⟨585375857531428831023845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390250571687619220682563 585375857531428831023845)
                ·
                  refine ⟨109757973287142905816971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 585375857531428831023845 109757973287142905816971)
                  ·
                    rfl

theorem cell21_480944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 4].length) (baseStart_480944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_480944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_480944 prefixEnd_480944 := by exact prefixLift 480944
  have htrace : WordTrace (prefixWord ++ tailWord_480944) baseStart_480944 baseEnd_480944 := by
    simpa [prefixWord, tailWord_480944, baseEnd_480944] using wordTrace_append hprefix tailTrace_480944
  have hstable : (prefixWord ++ tailWord_480944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480944).length < 2 ^ (prefixWord ++ tailWord_480944).sum := by decide
  have hdescent : baseEnd_480944 < baseStart_480944 := by decide
  rcases family_descends (prefixWord ++ tailWord_480944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480958 : List Nat := [4, 2, 1, 1, 2, 2, 2, 7]
def baseStart_480958 : Nat := 118140960795 + 480958 * 2 ^ 59
def prefixEnd_480958 : Nat := 4983230072969 + 3 ^ 40 * 480958 * 2
def baseEnd_480958 : Nat := 36587056092627330861203

theorem tailTrace_480958 : CollatzResearch.WordTrace tailWord_480958 prefixEnd_480958 36587056092627330861203 := by
  unfold tailWord_480958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2192747423947347741490441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11694652927719187954615685 2192747423947347741490441)
  ·
    refine ⟨1644560567960510806117831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2192747423947347741490441 1644560567960510806117831)
    ·
      refine ⟨2466840851940766209176747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1644560567960510806117831 2466840851940766209176747)
      ·
        refine ⟨3700261277911149313765121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2466840851940766209176747 3700261277911149313765121)
        ·
          refine ⟨2775195958433361985323841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3700261277911149313765121 2775195958433361985323841)
          ·
            refine ⟨2081396968825021488992881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2775195958433361985323841 2081396968825021488992881)
            ·
              refine ⟨1561047726618766116744661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2081396968825021488992881 1561047726618766116744661)
              ·
                refine ⟨36587056092627330861203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1561047726618766116744661 36587056092627330861203)
                ·
                  rfl

theorem cell21_480958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_480958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_480958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_480958 prefixEnd_480958 := by exact prefixLift 480958
  have htrace : WordTrace (prefixWord ++ tailWord_480958) baseStart_480958 baseEnd_480958 := by
    simpa [prefixWord, tailWord_480958, baseEnd_480958] using wordTrace_append hprefix tailTrace_480958
  have hstable : (prefixWord ++ tailWord_480958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480958).length < 2 ^ (prefixWord ++ tailWord_480958).sum := by decide
  have hdescent : baseEnd_480958 < baseStart_480958 := by decide
  rcases family_descends (prefixWord ++ tailWord_480958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481003 : List Nat := [1, 1, 1, 1, 2, 4, 4, 3, 4]
def baseStart_481003 : Nat := 118140960795 + 481003 * 2 ^ 59
def prefixEnd_481003 : Nat := 4983230072969 + 3 ^ 40 * 481003 * 2
def baseEnd_481003 : Nat := 109771437890971914333517

theorem tailTrace_481003 : CollatzResearch.WordTrace tailWord_481003 prefixEnd_481003 109771437890971914333517 := by
  unfold tailWord_481003
  simp only [CollatzResearch.WordTrace]
  refine ⟨17543620676415754617311663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11695747117610503078207775 17543620676415754617311663)
  ·
    refine ⟨26315431014623631925967495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17543620676415754617311663 26315431014623631925967495)
    ·
      refine ⟨39473146521935447888951243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26315431014623631925967495 39473146521935447888951243)
      ·
        refine ⟨59209719782903171833426865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39473146521935447888951243 59209719782903171833426865)
        ·
          refine ⟨44407289837177378875070149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59209719782903171833426865 44407289837177378875070149)
          ·
            refine ⟨8326366844470758539075653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44407289837177378875070149 8326366844470758539075653)
            ·
              refine ⟨1561193783338267226076685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8326366844470758539075653 1561193783338267226076685)
              ·
                refine ⟨585447668751850209778757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1561193783338267226076685 585447668751850209778757)
                ·
                  refine ⟨109771437890971914333517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 585447668751850209778757 109771437890971914333517)
                  ·
                    rfl

theorem cell21_481003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 4].length) (baseStart_481003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_481003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_481003 prefixEnd_481003 := by exact prefixLift 481003
  have htrace : WordTrace (prefixWord ++ tailWord_481003) baseStart_481003 baseEnd_481003 := by
    simpa [prefixWord, tailWord_481003, baseEnd_481003] using wordTrace_append hprefix tailTrace_481003
  have hstable : (prefixWord ++ tailWord_481003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481003).length < 2 ^ (prefixWord ++ tailWord_481003).sum := by decide
  have hdescent : baseEnd_481003 < baseStart_481003 := by decide
  rcases family_descends (prefixWord ++ tailWord_481003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481048 : List Nat := [2, 1, 2, 3, 1, 1, 3, 3, 5]
def baseStart_481048 : Nat := 118140960795 + 481048 * 2 ^ 59
def prefixEnd_481048 : Nat := 4983230072969 + 3 ^ 40 * 481048 * 2
def baseEnd_481048 : Nat := 109781707504061836083425

theorem tailTrace_481048 : CollatzResearch.WordTrace tailWord_481048 prefixEnd_481048 109781707504061836083425 := by
  unfold tailWord_481048
  simp only [CollatzResearch.WordTrace]
  refine ⟨8772630980626363651349899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11696841307501818201799865 8772630980626363651349899)
  ·
    refine ⟨13158946470939545477024849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8772630980626363651349899 13158946470939545477024849)
    ·
      refine ⟨9869209853204659107768637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13158946470939545477024849 9869209853204659107768637)
      ·
        refine ⟨3700953694951747165413239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9869209853204659107768637 3700953694951747165413239)
        ·
          refine ⟨5551430542427620748119859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3700953694951747165413239 5551430542427620748119859)
          ·
            refine ⟨8327145813641431122179789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5551430542427620748119859 8327145813641431122179789)
            ·
              refine ⟨3122679680115536670817421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8327145813641431122179789 3122679680115536670817421)
              ·
                refine ⟨1171004880043326251556533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3122679680115536670817421 1171004880043326251556533)
                ·
                  refine ⟨109781707504061836083425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1171004880043326251556533 109781707504061836083425)
                  ·
                    rfl

theorem cell21_481048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 5].length) (baseStart_481048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_481048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_481048 prefixEnd_481048 := by exact prefixLift 481048
  have htrace : WordTrace (prefixWord ++ tailWord_481048) baseStart_481048 baseEnd_481048 := by
    simpa [prefixWord, tailWord_481048, baseEnd_481048] using wordTrace_append hprefix tailTrace_481048
  have hstable : (prefixWord ++ tailWord_481048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481048).length < 2 ^ (prefixWord ++ tailWord_481048).sum := by decide
  have hdescent : baseEnd_481048 < baseStart_481048 := by decide
  rcases family_descends (prefixWord ++ tailWord_481048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481082 : List Nat := [3, 1, 1, 1, 5, 1, 3, 3, 3]
def baseStart_481082 : Nat := 118140960795 + 481082 * 2 ^ 59
def prefixEnd_481082 : Nat := 4983230072969 + 3 ^ 40 * 481082 * 2
def baseEnd_481082 : Nat := 109789466767285332516689

theorem tailTrace_481082 : CollatzResearch.WordTrace tailWord_481082 prefixEnd_481082 109789466767285332516689 := by
  unfold tailWord_481082
  simp only [CollatzResearch.WordTrace]
  refine ⟨4386625510782387777359375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11697668028753034072958333 4386625510782387777359375)
  ·
    refine ⟨6579938266173581666039063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4386625510782387777359375 6579938266173581666039063)
    ·
      refine ⟨9869907399260372499058595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6579938266173581666039063 9869907399260372499058595)
      ·
        refine ⟨14804861098890558748587893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9869907399260372499058595 14804861098890558748587893)
        ·
          refine ⟨1387955728020989882680115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14804861098890558748587893 1387955728020989882680115)
          ·
            refine ⟨2081933592031484824020173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1387955728020989882680115 2081933592031484824020173)
            ·
              refine ⟨780725097011806809007565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2081933592031484824020173 780725097011806809007565)
              ·
                refine ⟨292771911379427553377837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 780725097011806809007565 292771911379427553377837)
                ·
                  refine ⟨109789466767285332516689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 292771911379427553377837 109789466767285332516689)
                  ·
                    rfl

theorem cell21_481082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 3, 3].length) (baseStart_481082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_481082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_481082 prefixEnd_481082 := by exact prefixLift 481082
  have htrace : WordTrace (prefixWord ++ tailWord_481082) baseStart_481082 baseEnd_481082 := by
    simpa [prefixWord, tailWord_481082, baseEnd_481082] using wordTrace_append hprefix tailTrace_481082
  have hstable : (prefixWord ++ tailWord_481082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481082).length < 2 ^ (prefixWord ++ tailWord_481082).sum := by decide
  have hdescent : baseEnd_481082 < baseStart_481082 := by decide
  rcases family_descends (prefixWord ++ tailWord_481082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481155 : List Nat := [1, 1, 1, 3, 4, 2, 1, 4, 4]
def baseStart_481155 : Nat := 118140960795 + 481155 * 2 ^ 59
def prefixEnd_481155 : Nat := 4983230072969 + 3 ^ 40 * 481155 * 2
def baseEnd_481155 : Nat := 109806126361853427799873

theorem tailTrace_481155 : CollatzResearch.WordTrace tailWord_481155 prefixEnd_481155 109806126361853427799873 := by
  unfold tailWord_481155
  simp only [CollatzResearch.WordTrace]
  refine ⟨17549164571865084576844919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11699443047910056384563279 17549164571865084576844919)
  ·
    refine ⟨26323746857797626865267379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17549164571865084576844919 26323746857797626865267379)
    ·
      refine ⟨39485620286696440297901069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26323746857797626865267379 39485620286696440297901069)
      ·
        refine ⟨14807107607511165111712901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39485620286696440297901069 14807107607511165111712901)
        ·
          refine ⟨2776332676408343458446169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14807107607511165111712901 2776332676408343458446169)
          ·
            refine ⟨2082249507306257593834627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2776332676408343458446169 2082249507306257593834627)
            ·
              refine ⟨3123374260959386390751941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2082249507306257593834627 3123374260959386390751941)
              ·
                refine ⟨585632673929884948265989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3123374260959386390751941 585632673929884948265989)
                ·
                  refine ⟨109806126361853427799873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 585632673929884948265989 109806126361853427799873)
                  ·
                    rfl

theorem cell21_481155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 4].length) (baseStart_481155 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_481155 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_481155 prefixEnd_481155 := by exact prefixLift 481155
  have htrace : WordTrace (prefixWord ++ tailWord_481155) baseStart_481155 baseEnd_481155 := by
    simpa [prefixWord, tailWord_481155, baseEnd_481155] using wordTrace_append hprefix tailTrace_481155
  have hstable : (prefixWord ++ tailWord_481155).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481155).length < 2 ^ (prefixWord ++ tailWord_481155).sum := by decide
  have hdescent : baseEnd_481155 < baseStart_481155 := by decide
  rcases family_descends (prefixWord ++ tailWord_481155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481169 : List Nat := [1, 2, 2, 1, 1, 1, 7, 6]
def baseStart_481169 : Nat := 118140960795 + 481169 * 2 ^ 59
def prefixEnd_481169 : Nat := 4983230072969 + 3 ^ 40 * 481169 * 2
def baseEnd_481169 : Nat := 36603107117530838188837

theorem tailTrace_481169 : CollatzResearch.WordTrace tailWord_481169 prefixEnd_481169 36603107117530838188837 := by
  unfold tailWord_481169
  simp only [CollatzResearch.WordTrace]
  refine ⟨17549675193814364967854561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11699783462542909978569707 17549675193814364967854561)
  ·
    refine ⟨13162256395360773725890921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17549675193814364967854561 13162256395360773725890921)
    ·
      refine ⟨9871692296520580294418191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13162256395360773725890921 9871692296520580294418191)
      ·
        refine ⟨14807538444780870441627287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9871692296520580294418191 14807538444780870441627287)
        ·
          refine ⟨22211307667171305662440931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14807538444780870441627287 22211307667171305662440931)
          ·
            refine ⟨33316961500756958493661397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22211307667171305662440931 33316961500756958493661397)
            ·
              refine ⟨780866285173991214695189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 33316961500756958493661397 780866285173991214695189)
              ·
                refine ⟨36603107117530838188837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 780866285173991214695189 36603107117530838188837)
                ·
                  rfl

theorem cell21_481169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 6].length) (baseStart_481169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_481169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_481169 prefixEnd_481169 := by exact prefixLift 481169
  have htrace : WordTrace (prefixWord ++ tailWord_481169) baseStart_481169 baseEnd_481169 := by
    simpa [prefixWord, tailWord_481169, baseEnd_481169] using wordTrace_append hprefix tailTrace_481169
  have hstable : (prefixWord ++ tailWord_481169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481169).length < 2 ^ (prefixWord ++ tailWord_481169).sum := by decide
  have hdescent : baseEnd_481169 < baseStart_481169 := by decide
  rcases family_descends (prefixWord ++ tailWord_481169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481172 : List Nat := [2, 4, 2, 1, 1, 2, 2, 3, 4]
def baseStart_481172 : Nat := 118140960795 + 481172 * 2 ^ 59
def prefixEnd_481172 : Nat := 4983230072969 + 3 ^ 40 * 481172 * 2
def baseEnd_481172 : Nat := 109810005993465176016505

theorem tailTrace_481172 : CollatzResearch.WordTrace tailWord_481172 prefixEnd_481172 109810005993465176016505 := by
  unfold tailWord_481172
  simp only [CollatzResearch.WordTrace]
  refine ⟨8774892306401748240106885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11699856408535664320142513 8774892306401748240106885)
  ·
    refine ⟨1645292307450327795020041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8774892306401748240106885 1645292307450327795020041)
    ·
      refine ⟨1233969230587745846265031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1645292307450327795020041 1233969230587745846265031)
      ·
        refine ⟨1850953845881618769397547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1233969230587745846265031 1850953845881618769397547)
        ·
          refine ⟨2776430768822428154096321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1850953845881618769397547 2776430768822428154096321)
          ·
            refine ⟨2082323076616821115572241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2776430768822428154096321 2082323076616821115572241)
            ·
              refine ⟨1561742307462615836679181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2082323076616821115572241 1561742307462615836679181)
              ·
                refine ⟨585653365298480938754693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1561742307462615836679181 585653365298480938754693)
                ·
                  refine ⟨109810005993465176016505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 585653365298480938754693 109810005993465176016505)
                  ·
                    rfl

theorem cell21_481172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_481172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_481172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_481172 prefixEnd_481172 := by exact prefixLift 481172
  have htrace : WordTrace (prefixWord ++ tailWord_481172) baseStart_481172 baseEnd_481172 := by
    simpa [prefixWord, tailWord_481172, baseEnd_481172] using wordTrace_append hprefix tailTrace_481172
  have hstable : (prefixWord ++ tailWord_481172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481172).length < 2 ^ (prefixWord ++ tailWord_481172).sum := by decide
  have hdescent : baseEnd_481172 < baseStart_481172 := by decide
  rcases family_descends (prefixWord ++ tailWord_481172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481192 : List Nat := [2, 1, 6, 2, 1, 1, 2, 3, 3]
def baseStart_481192 : Nat := 118140960795 + 481192 * 2 ^ 59
def prefixEnd_481192 : Nat := 4983230072969 + 3 ^ 40 * 481192 * 2
def baseEnd_481192 : Nat := 109814570265949585683131

theorem tailTrace_481192 : CollatzResearch.WordTrace tailWord_481192 prefixEnd_481192 109814570265949585683131 := by
  unfold tailWord_481192
  simp only [CollatzResearch.WordTrace]
  refine ⟨8775257036365519947970915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11700342715154026597294553 8775257036365519947970915)
  ·
    refine ⟨13162885554548279921956373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8775257036365519947970915 13162885554548279921956373)
    ·
      refine ⟨617010260369450621341705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13162885554548279921956373 617010260369450621341705)
      ·
        refine ⟨462757695277087966006279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 617010260369450621341705 462757695277087966006279)
        ·
          refine ⟨694136542915631949009419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462757695277087966006279 694136542915631949009419)
          ·
            refine ⟨1041204814373447923514129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694136542915631949009419 1041204814373447923514129)
            ·
              refine ⟨780903610780085942635597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1041204814373447923514129 780903610780085942635597)
              ·
                refine ⟨292838854042532228488349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 780903610780085942635597 292838854042532228488349)
                ·
                  refine ⟨109814570265949585683131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 292838854042532228488349 109814570265949585683131)
                  ·
                    rfl

theorem cell21_481192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 3, 3].length) (baseStart_481192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_481192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_481192 prefixEnd_481192 := by exact prefixLift 481192
  have htrace : WordTrace (prefixWord ++ tailWord_481192) baseStart_481192 baseEnd_481192 := by
    simpa [prefixWord, tailWord_481192, baseEnd_481192] using wordTrace_append hprefix tailTrace_481192
  have hstable : (prefixWord ++ tailWord_481192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481192).length < 2 ^ (prefixWord ++ tailWord_481192).sum := by decide
  have hdescent : baseEnd_481192 < baseStart_481192 := by decide
  rcases family_descends (prefixWord ++ tailWord_481192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481259 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 7]
def baseStart_481259 : Nat := 118140960795 + 481259 * 2 ^ 59
def prefixEnd_481259 : Nat := 4983230072969 + 3 ^ 40 * 481259 * 2
def baseEnd_481259 : Nat := 109829860578772358066327

theorem tailTrace_481259 : CollatzResearch.WordTrace tailWord_481259 prefixEnd_481259 109829860578772358066327 := by
  unfold tailWord_481259
  simp only [CollatzResearch.WordTrace]
  refine ⟨17552957763488310338630831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11701971842325540225753887 17552957763488310338630831)
  ·
    refine ⟨26329436645232465507946247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17552957763488310338630831 26329436645232465507946247)
    ·
      refine ⟨39494154967848698261919371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26329436645232465507946247 39494154967848698261919371)
      ·
        refine ⟨59241232451773047392879057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39494154967848698261919371 59241232451773047392879057)
        ·
          refine ⟨44430924338829785544659293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59241232451773047392879057 44430924338829785544659293)
          ·
            refine ⟨16661596627061169579247235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44430924338829785544659293 16661596627061169579247235)
            ·
              refine ⟨24992394940591754368870853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16661596627061169579247235 24992394940591754368870853)
              ·
                refine ⟨4686074051360953944163285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24992394940591754368870853 4686074051360953944163285)
                ·
                  refine ⟨109829860578772358066327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4686074051360953944163285 109829860578772358066327)
                  ·
                    rfl

theorem cell21_481259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 7].length) (baseStart_481259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_481259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_481259 prefixEnd_481259 := by exact prefixLift 481259
  have htrace : WordTrace (prefixWord ++ tailWord_481259) baseStart_481259 baseEnd_481259 := by
    simpa [prefixWord, tailWord_481259, baseEnd_481259] using wordTrace_append hprefix tailTrace_481259
  have hstable : (prefixWord ++ tailWord_481259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481259).length < 2 ^ (prefixWord ++ tailWord_481259).sum := by decide
  have hdescent : baseEnd_481259 < baseStart_481259 := by decide
  rcases family_descends (prefixWord ++ tailWord_481259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481262 : List Nat := [4, 1, 2, 1, 3, 3, 7]
def baseStart_481262 : Nat := 118140960795 + 481262 * 2 ^ 59
def prefixEnd_481262 : Nat := 4983230072969 + 3 ^ 40 * 481262 * 2
def baseEnd_481262 : Nat := 12203393913293891057369

theorem tailTrace_481262 : CollatzResearch.WordTrace tailWord_481262 prefixEnd_481262 12203393913293891057369 := by
  unfold tailWord_481262
  simp only [CollatzResearch.WordTrace]
  refine ⟨2194133397809680231373755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11702044788318294567326693 2194133397809680231373755)
  ·
    refine ⟨3291200096714520347060633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2194133397809680231373755 3291200096714520347060633)
    ·
      refine ⟨2468400072535890260295475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3291200096714520347060633 2468400072535890260295475)
      ·
        refine ⟨3702600108803835390443213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2468400072535890260295475 3702600108803835390443213)
        ·
          refine ⟨1388475040801438271416205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3702600108803835390443213 1388475040801438271416205)
          ·
            refine ⟨520678140300539351781077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1388475040801438271416205 520678140300539351781077)
            ·
              refine ⟨12203393913293891057369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 520678140300539351781077 12203393913293891057369)
              ·
                rfl

theorem cell21_481262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 7].length) (baseStart_481262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_481262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_481262 prefixEnd_481262 := by exact prefixLift 481262
  have htrace : WordTrace (prefixWord ++ tailWord_481262) baseStart_481262 baseEnd_481262 := by
    simpa [prefixWord, tailWord_481262, baseEnd_481262] using wordTrace_append hprefix tailTrace_481262
  have hstable : (prefixWord ++ tailWord_481262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481262).length < 2 ^ (prefixWord ++ tailWord_481262).sum := by decide
  have hdescent : baseEnd_481262 < baseStart_481262 := by decide
  rcases family_descends (prefixWord ++ tailWord_481262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481369 : List Nat := [1, 2, 1, 2, 2, 1, 6, 3, 3]
def baseStart_481369 : Nat := 118140960795 + 481369 * 2 ^ 59
def prefixEnd_481369 : Nat := 4983230072969 + 3 ^ 40 * 481369 * 2
def baseEnd_481369 : Nat := 109854964077436611232769

theorem tailTrace_481369 : CollatzResearch.WordTrace tailWord_481369 prefixEnd_481369 109854964077436611232769 := by
  unfold tailWord_481369
  simp only [CollatzResearch.WordTrace]
  refine ⟨17556969793089799125135161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11704646528726532750090107 17556969793089799125135161)
  ·
    refine ⟨13167727344817349343851371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17556969793089799125135161 13167727344817349343851371)
    ·
      refine ⟨19751591017226024015777057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13167727344817349343851371 19751591017226024015777057)
      ·
        refine ⟨14813693262919518011832793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19751591017226024015777057 14813693262919518011832793)
        ·
          refine ⟨11110269947189638508874595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14813693262919518011832793 11110269947189638508874595)
          ·
            refine ⟨16665404920784457763311893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11110269947189638508874595 16665404920784457763311893)
            ·
              refine ⟨781190855661771457655245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16665404920784457763311893 781190855661771457655245)
              ·
                refine ⟨292946570873164296620717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 781190855661771457655245 292946570873164296620717)
                ·
                  refine ⟨109854964077436611232769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 292946570873164296620717 109854964077436611232769)
                  ·
                    rfl

theorem cell21_481369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 3, 3].length) (baseStart_481369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_481369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_481369 prefixEnd_481369 := by exact prefixLift 481369
  have htrace : WordTrace (prefixWord ++ tailWord_481369) baseStart_481369 baseEnd_481369 := by
    simpa [prefixWord, tailWord_481369, baseEnd_481369] using wordTrace_append hprefix tailTrace_481369
  have hstable : (prefixWord ++ tailWord_481369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481369).length < 2 ^ (prefixWord ++ tailWord_481369).sum := by decide
  have hdescent : baseEnd_481369 < baseStart_481369 := by decide
  rcases family_descends (prefixWord ++ tailWord_481369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481507 : List Nat := [1, 1, 1, 8, 1, 2, 1, 6]
def baseStart_481507 : Nat := 118140960795 + 481507 * 2 ^ 59
def prefixEnd_481507 : Nat := 4983230072969 + 3 ^ 40 * 481507 * 2
def baseEnd_481507 : Nat := 36628819185859679310829

theorem tailTrace_481507 : CollatzResearch.WordTrace tailWord_481507 prefixEnd_481507 36628819185859679310829 := by
  unfold tailWord_481507
  simp only [CollatzResearch.WordTrace]
  refine ⟨17562003066589848693658775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11708002044393232462439183 17562003066589848693658775)
  ·
    refine ⟨26343004599884773040488163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17562003066589848693658775 26343004599884773040488163)
    ·
      refine ⟨39514506899827159560732245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26343004599884773040488163 39514506899827159560732245)
      ·
        refine ⟨463060627732349526102331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 39514506899827159560732245 463060627732349526102331)
        ·
          refine ⟨694590941598524289153497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463060627732349526102331 694590941598524289153497)
          ·
            refine ⟨520943206198893216865123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 694590941598524289153497 520943206198893216865123)
            ·
              refine ⟨781414809298339825297685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520943206198893216865123 781414809298339825297685)
              ·
                refine ⟨36628819185859679310829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 781414809298339825297685 36628819185859679310829)
                ·
                  rfl

theorem cell21_481507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 6].length) (baseStart_481507 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_481507 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_481507 prefixEnd_481507 := by exact prefixLift 481507
  have htrace : WordTrace (prefixWord ++ tailWord_481507) baseStart_481507 baseEnd_481507 := by
    simpa [prefixWord, tailWord_481507, baseEnd_481507] using wordTrace_append hprefix tailTrace_481507
  have hstable : (prefixWord ++ tailWord_481507).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481507).length < 2 ^ (prefixWord ++ tailWord_481507).sum := by decide
  have hdescent : baseEnd_481507 < baseStart_481507 := by decide
  rcases family_descends (prefixWord ++ tailWord_481507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481518 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 8]
def baseStart_481518 : Nat := 118140960795 + 481518 * 2 ^ 59
def prefixEnd_481518 : Nat := 4983230072969 + 3 ^ 40 * 481518 * 2
def baseEnd_481518 : Nat := 109888967907445463249131

theorem tailTrace_481518 : CollatzResearch.WordTrace tailWord_481518 prefixEnd_481518 109888967907445463249131 := by
  unfold tailWord_481518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2195300533693749696538651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11708269513033331714872805 2195300533693749696538651)
  ·
    refine ⟨3292950800540624544807977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2195300533693749696538651 3292950800540624544807977)
    ·
      refine ⟨2469713100405468408605983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3292950800540624544807977 2469713100405468408605983)
      ·
        refine ⟨3704569650608202612908975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2469713100405468408605983 3704569650608202612908975)
        ·
          refine ⟨5556854475912303919363463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3704569650608202612908975 5556854475912303919363463)
          ·
            refine ⟨8335281713868455879045195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5556854475912303919363463 8335281713868455879045195)
            ·
              refine ⟨12502922570802683818567793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8335281713868455879045195 12502922570802683818567793)
              ·
                refine ⟨9377191928102012863925845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12502922570802683818567793 9377191928102012863925845)
                ·
                  refine ⟨109888967907445463249131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9377191928102012863925845 109888967907445463249131)
                  ·
                    rfl

theorem cell21_481518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_481518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_481518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_481518 prefixEnd_481518 := by exact prefixLift 481518
  have htrace : WordTrace (prefixWord ++ tailWord_481518) baseStart_481518 baseEnd_481518 := by
    simpa [prefixWord, tailWord_481518, baseEnd_481518] using wordTrace_append hprefix tailTrace_481518
  have hstable : (prefixWord ++ tailWord_481518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481518).length < 2 ^ (prefixWord ++ tailWord_481518).sum := by decide
  have hdescent : baseEnd_481518 < baseStart_481518 := by decide
  rcases family_descends (prefixWord ++ tailWord_481518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481538 : List Nat := [3, 4, 1, 1, 2, 1, 1, 5, 3]
def baseStart_481538 : Nat := 118140960795 + 481538 * 2 ^ 59
def prefixEnd_481538 : Nat := 4983230072969 + 3 ^ 40 * 481538 * 2
def baseEnd_481538 : Nat := 109893532179929872915757

theorem tailTrace_481538 : CollatzResearch.WordTrace tailWord_481538 prefixEnd_481538 109893532179929872915757 := by
  unfold tailWord_481538
  simp only [CollatzResearch.WordTrace]
  refine ⟨4390783432369385247009317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11708755819651693992024845 4390783432369385247009317)
  ·
    refine ⟨823271893569259733814247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4390783432369385247009317 823271893569259733814247)
    ·
      refine ⟨1234907840353889600721371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 823271893569259733814247 1234907840353889600721371)
      ·
        refine ⟨1852361760530834401082057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1234907840353889600721371 1852361760530834401082057)
        ·
          refine ⟨1389271320398125800811543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1852361760530834401082057 1389271320398125800811543)
          ·
            refine ⟨2083906980597188701217315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1389271320398125800811543 2083906980597188701217315)
            ·
              refine ⟨3125860470895783051825973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2083906980597188701217315 3125860470895783051825973)
              ·
                refine ⟨293049419146479661108685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3125860470895783051825973 293049419146479661108685)
                ·
                  refine ⟨109893532179929872915757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 293049419146479661108685 109893532179929872915757)
                  ·
                    rfl

theorem cell21_481538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_481538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_481538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_481538 prefixEnd_481538 := by exact prefixLift 481538
  have htrace : WordTrace (prefixWord ++ tailWord_481538) baseStart_481538 baseEnd_481538 := by
    simpa [prefixWord, tailWord_481538, baseEnd_481538] using wordTrace_append hprefix tailTrace_481538
  have hstable : (prefixWord ++ tailWord_481538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481538).length < 2 ^ (prefixWord ++ tailWord_481538).sum := by decide
  have hdescent : baseEnd_481538 < baseStart_481538 := by decide
  rcases family_descends (prefixWord ++ tailWord_481538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481563 : List Nat := [1, 1, 1, 1, 1, 1, 7, 3, 5]
def baseStart_481563 : Nat := 118140960795 + 481563 * 2 ^ 59
def prefixEnd_481563 : Nat := 4983230072969 + 3 ^ 40 * 481563 * 2
def baseEnd_481563 : Nat := 109899237520535384999039

theorem tailTrace_481563 : CollatzResearch.WordTrace tailWord_481563 prefixEnd_481563 109899237520535384999039 := by
  unfold tailWord_481563
  simp only [CollatzResearch.WordTrace]
  refine ⟨17564045554386970257697343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11709363702924646838464895 17564045554386970257697343)
  ·
    refine ⟨26346068331580455386546015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17564045554386970257697343 26346068331580455386546015)
    ·
      refine ⟨39519102497370683079819023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26346068331580455386546015 39519102497370683079819023)
      ·
        refine ⟨59278653746056024619728535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39519102497370683079819023 59278653746056024619728535)
        ·
          refine ⟨88917980619084036929592803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59278653746056024619728535 88917980619084036929592803)
          ·
            refine ⟨133376970928626055394389205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88917980619084036929592803 133376970928626055394389205)
            ·
              refine ⟨3126022756139673173305997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 133376970928626055394389205 3126022756139673173305997)
              ·
                refine ⟨1172258533552377439989749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3126022756139673173305997 1172258533552377439989749)
                ·
                  refine ⟨109899237520535384999039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1172258533552377439989749 109899237520535384999039)
                  ·
                    rfl

theorem cell21_481563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 5].length) (baseStart_481563 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_481563 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_481563 prefixEnd_481563 := by exact prefixLift 481563
  have htrace : WordTrace (prefixWord ++ tailWord_481563) baseStart_481563 baseEnd_481563 := by
    simpa [prefixWord, tailWord_481563, baseEnd_481563] using wordTrace_append hprefix tailTrace_481563
  have hstable : (prefixWord ++ tailWord_481563).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481563).length < 2 ^ (prefixWord ++ tailWord_481563).sum := by decide
  have hdescent : baseEnd_481563 < baseStart_481563 := by decide
  rcases family_descends (prefixWord ++ tailWord_481563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481594 : List Nat := [3, 1, 1, 1, 4, 2, 1, 2, 6]
def baseStart_481594 : Nat := 118140960795 + 481594 * 2 ^ 59
def prefixEnd_481594 : Nat := 4983230072969 + 3 ^ 40 * 481594 * 2
def baseEnd_481594 : Nat := 109906312142886219982309

theorem tailTrace_481594 : CollatzResearch.WordTrace tailWord_481594 prefixEnd_481594 109906312142886219982309 := by
  unfold tailWord_481594
  simp only [CollatzResearch.WordTrace]
  refine ⟨4391294054318665638018959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11710117478183108368050557 4391294054318665638018959)
  ·
    refine ⟨6586941081477998457028439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4391294054318665638018959 6586941081477998457028439)
    ·
      refine ⟨9880411622216997685542659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6586941081477998457028439 9880411622216997685542659)
      ·
        refine ⟨14820617433325496528313989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9880411622216997685542659 14820617433325496528313989)
        ·
          refine ⟨2778865768748530599058873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14820617433325496528313989 2778865768748530599058873)
          ·
            refine ⟨2084149326561397949294155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2778865768748530599058873 2084149326561397949294155)
            ·
              refine ⟨3126223989842096923941233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2084149326561397949294155 3126223989842096923941233)
              ·
                refine ⟨2344667992381572692955925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3126223989842096923941233 2344667992381572692955925)
                ·
                  refine ⟨109906312142886219982309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2344667992381572692955925 109906312142886219982309)
                  ·
                    rfl

theorem cell21_481594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_481594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_481594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_481594 prefixEnd_481594 := by exact prefixLift 481594
  have htrace : WordTrace (prefixWord ++ tailWord_481594) baseStart_481594 baseEnd_481594 := by
    simpa [prefixWord, tailWord_481594, baseEnd_481594] using wordTrace_append hprefix tailTrace_481594
  have hstable : (prefixWord ++ tailWord_481594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481594).length < 2 ^ (prefixWord ++ tailWord_481594).sum := by decide
  have hdescent : baseEnd_481594 < baseStart_481594 := by decide
  rcases family_descends (prefixWord ++ tailWord_481594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481608 : List Nat := [2, 1, 3, 1, 1, 2, 11]
def baseStart_481608 : Nat := 118140960795 + 481608 * 2 ^ 59
def prefixEnd_481608 : Nat := 4983230072969 + 3 ^ 40 * 481608 * 2
def baseEnd_481608 : Nat := 12212167459291700749883

theorem tailTrace_481608 : CollatzResearch.WordTrace tailWord_481608 prefixEnd_481608 12212167459291700749883 := by
  unfold tailWord_481608
  simp only [CollatzResearch.WordTrace]
  refine ⟨8782843419611971471542739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11710457892815961962056985 8782843419611971471542739)
  ·
    refine ⟨13174265129417957207314109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8782843419611971471542739 13174265129417957207314109)
    ·
      refine ⟨4940349423531733952742791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13174265129417957207314109 4940349423531733952742791)
      ·
        refine ⟨7410524135297600929114187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4940349423531733952742791 7410524135297600929114187)
        ·
          refine ⟨11115786202946401393671281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7410524135297600929114187 11115786202946401393671281)
          ·
            refine ⟨8336839652209801045253461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11115786202946401393671281 8336839652209801045253461)
            ·
              refine ⟨12212167459291700749883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 8336839652209801045253461 12212167459291700749883)
              ·
                rfl

theorem cell21_481608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 11].length) (baseStart_481608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_481608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_481608 prefixEnd_481608 := by exact prefixLift 481608
  have htrace : WordTrace (prefixWord ++ tailWord_481608) baseStart_481608 baseEnd_481608 := by
    simpa [prefixWord, tailWord_481608, baseEnd_481608] using wordTrace_append hprefix tailTrace_481608
  have hstable : (prefixWord ++ tailWord_481608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481608).length < 2 ^ (prefixWord ++ tailWord_481608).sum := by decide
  have hdescent : baseEnd_481608 < baseStart_481608 := by decide
  rcases family_descends (prefixWord ++ tailWord_481608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481673 : List Nat := [1, 2, 1, 1, 6, 2, 1, 4, 3]
def baseStart_481673 : Nat := 118140960795 + 481673 * 2 ^ 59
def prefixEnd_481673 : Nat := 4983230072969 + 3 ^ 40 * 481673 * 2
def baseEnd_481673 : Nat := 109924341019199638165481

theorem tailTrace_481673 : CollatzResearch.WordTrace tailWord_481673 prefixEnd_481673 109924341019199638165481 := by
  unfold tailWord_481673
  simp only [CollatzResearch.WordTrace]
  refine ⟨17568057583988459044201673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11712038389325639362801115 17568057583988459044201673)
  ·
    refine ⟨13176043187991344283151255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17568057583988459044201673 13176043187991344283151255)
    ·
      refine ⟨19764064781987016424726883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13176043187991344283151255 19764064781987016424726883)
      ·
        refine ⟨29646097172980524637090325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19764064781987016424726883 29646097172980524637090325)
        ·
          refine ⟨1389660804983462092363609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29646097172980524637090325 1389660804983462092363609)
          ·
            refine ⟨1042245603737596569272707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1389660804983462092363609 1042245603737596569272707)
            ·
              refine ⟨1563368405606394853909061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1042245603737596569272707 1563368405606394853909061)
              ·
                refine ⟨293131576051199035107949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1563368405606394853909061 293131576051199035107949)
                ·
                  refine ⟨109924341019199638165481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 293131576051199035107949 109924341019199638165481)
                  ·
                    rfl

theorem cell21_481673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 4, 3].length) (baseStart_481673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_481673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_481673 prefixEnd_481673 := by exact prefixLift 481673
  have htrace : WordTrace (prefixWord ++ tailWord_481673) baseStart_481673 baseEnd_481673 := by
    simpa [prefixWord, tailWord_481673, baseEnd_481673] using wordTrace_append hprefix tailTrace_481673
  have hstable : (prefixWord ++ tailWord_481673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481673).length < 2 ^ (prefixWord ++ tailWord_481673).sum := by decide
  have hdescent : baseEnd_481673 < baseStart_481673 := by decide
  rcases family_descends (prefixWord ++ tailWord_481673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481701 : List Nat := [1, 3, 1, 2, 1, 1, 7, 5]
def baseStart_481701 : Nat := 118140960795 + 481701 * 2 ^ 59
def prefixEnd_481701 : Nat := 4983230072969 + 3 ^ 40 * 481701 * 2
def baseEnd_481701 : Nat := 36643577000225937232919

theorem tailTrace_481701 : CollatzResearch.WordTrace tailWord_481701 prefixEnd_481701 36643577000225937232919 := by
  unfold tailWord_481701
  simp only [CollatzResearch.WordTrace]
  refine ⟨17569078827887019826220957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11712719218591346550813971 17569078827887019826220957)
  ·
    refine ⟨6588404560457632434832859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17569078827887019826220957 6588404560457632434832859)
    ·
      refine ⟨9882606840686448652249289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6588404560457632434832859 9882606840686448652249289)
      ·
        refine ⟨7411955130514836489186967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9882606840686448652249289 7411955130514836489186967)
        ·
          refine ⟨11117932695772254733780451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7411955130514836489186967 11117932695772254733780451)
          ·
            refine ⟨16676899043658382100670677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11117932695772254733780451 16676899043658382100670677)
            ·
              refine ⟨390864821335743330484469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 16676899043658382100670677 390864821335743330484469)
              ·
                refine ⟨36643577000225937232919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 390864821335743330484469 36643577000225937232919)
                ·
                  rfl

theorem cell21_481701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 5].length) (baseStart_481701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_481701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_481701 prefixEnd_481701 := by exact prefixLift 481701
  have htrace : WordTrace (prefixWord ++ tailWord_481701) baseStart_481701 baseEnd_481701 := by
    simpa [prefixWord, tailWord_481701, baseEnd_481701] using wordTrace_append hprefix tailTrace_481701
  have hstable : (prefixWord ++ tailWord_481701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481701).length < 2 ^ (prefixWord ++ tailWord_481701).sum := by decide
  have hdescent : baseEnd_481701 < baseStart_481701 := by decide
  rcases family_descends (prefixWord ++ tailWord_481701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481760 : List Nat := [2, 1, 1, 3, 1, 1, 5, 7]
def baseStart_481760 : Nat := 118140960795 + 481760 * 2 ^ 59
def prefixEnd_481760 : Nat := 4983230072969 + 3 ^ 40 * 481760 * 2
def baseEnd_481760 : Nat := 36648065201502273405101

theorem tailTrace_481760 : CollatzResearch.WordTrace tailWord_481760 prefixEnd_481760 36648065201502273405101 := by
  unfold tailWord_481760
  simp only [CollatzResearch.WordTrace]
  refine ⟨8785615367336636451309367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11714153823115515268412489 8785615367336636451309367)
  ·
    refine ⟨13178423051004954676964051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8785615367336636451309367 13178423051004954676964051)
    ·
      refine ⟨19767634576507432015446077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13178423051004954676964051 19767634576507432015446077)
      ·
        refine ⟨7412862966190287005792279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19767634576507432015446077 7412862966190287005792279)
        ·
          refine ⟨11119294449285430508688419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7412862966190287005792279 11119294449285430508688419)
          ·
            refine ⟨16678941673928145763032629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11119294449285430508688419 16678941673928145763032629)
            ·
              refine ⟨1563650781930763665284309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16678941673928145763032629 1563650781930763665284309)
              ·
                refine ⟨36648065201502273405101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1563650781930763665284309 36648065201502273405101)
                ·
                  rfl

theorem cell21_481760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 7].length) (baseStart_481760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_481760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_481760 prefixEnd_481760 := by exact prefixLift 481760
  have htrace : WordTrace (prefixWord ++ tailWord_481760) baseStart_481760 baseEnd_481760 := by
    simpa [prefixWord, tailWord_481760, baseEnd_481760] using wordTrace_append hprefix tailTrace_481760
  have hstable : (prefixWord ++ tailWord_481760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481760).length < 2 ^ (prefixWord ++ tailWord_481760).sum := by decide
  have hdescent : baseEnd_481760 < baseStart_481760 := by decide
  rcases family_descends (prefixWord ++ tailWord_481760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481853 : List Nat := [1, 4, 1, 3, 2, 1, 3, 6]
def baseStart_481853 : Nat := 118140960795 + 481853 * 2 ^ 59
def prefixEnd_481853 : Nat := 4983230072969 + 3 ^ 40 * 481853 * 2
def baseEnd_481853 : Nat := 36655139823853108388371

theorem tailTrace_481853 : CollatzResearch.WordTrace tailWord_481853 prefixEnd_481853 36655139823853108388371 := by
  unfold tailWord_481853
  simp only [CollatzResearch.WordTrace]
  refine ⟨17574622723336349785754213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11716415148890899857169475 17574622723336349785754213)
  ·
    refine ⟨3295241760625565584828915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17574622723336349785754213 3295241760625565584828915)
    ·
      refine ⟨4942862640938348377243373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3295241760625565584828915 4942862640938348377243373)
      ·
        refine ⟨1853573490351880641466265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4942862640938348377243373 1853573490351880641466265)
        ·
          refine ⟨1390180117763910481099699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1853573490351880641466265 1390180117763910481099699)
          ·
            refine ⟨2085270176645865721649549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1390180117763910481099699 2085270176645865721649549)
            ·
              refine ⟨781976316242199645618581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2085270176645865721649549 781976316242199645618581)
              ·
                refine ⟨36655139823853108388371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 781976316242199645618581 36655139823853108388371)
                ·
                  rfl

theorem cell21_481853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 6].length) (baseStart_481853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_481853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_481853 prefixEnd_481853 := by exact prefixLift 481853
  have htrace : WordTrace (prefixWord ++ tailWord_481853) baseStart_481853 baseEnd_481853 := by
    simpa [prefixWord, tailWord_481853, baseEnd_481853] using wordTrace_append hprefix tailTrace_481853
  have hstable : (prefixWord ++ tailWord_481853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481853).length < 2 ^ (prefixWord ++ tailWord_481853).sum := by decide
  have hdescent : baseEnd_481853 < baseStart_481853 := by decide
  rcases family_descends (prefixWord ++ tailWord_481853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481890 : List Nat := [3, 3, 2, 3, 2, 1, 1, 2, 4]
def baseStart_481890 : Nat := 118140960795 + 481890 * 2 ^ 59
def prefixEnd_481890 : Nat := 4983230072969 + 3 ^ 40 * 481890 * 2
def baseEnd_481890 : Nat := 109973863375655483048371

theorem tailTrace_481890 : CollatzResearch.WordTrace tailWord_481890 prefixEnd_481890 109973863375655483048371 := by
  unfold tailWord_481890
  simp only [CollatzResearch.WordTrace]
  refine ⟨4393993056050576276212781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11717314816134870069900749 4393993056050576276212781)
  ·
    refine ⟨1647747396018966103579793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4393993056050576276212781 1647747396018966103579793)
    ·
      refine ⟨1235810547014224577684845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1647747396018966103579793 1235810547014224577684845)
      ·
        refine ⟨463428955130334216631817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1235810547014224577684845 463428955130334216631817)
        ·
          refine ⟨347571716347750662473863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463428955130334216631817 347571716347750662473863)
          ·
            refine ⟨521357574521625993710795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347571716347750662473863 521357574521625993710795)
            ·
              refine ⟨782036361782438990566193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521357574521625993710795 782036361782438990566193)
              ·
                refine ⟨586527271336829242924645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 782036361782438990566193 586527271336829242924645)
                ·
                  refine ⟨109973863375655483048371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 586527271336829242924645 109973863375655483048371)
                  ·
                    rfl

theorem cell21_481890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_481890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_481890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_481890 prefixEnd_481890 := by exact prefixLift 481890
  have htrace : WordTrace (prefixWord ++ tailWord_481890) baseStart_481890 baseEnd_481890 := by
    simpa [prefixWord, tailWord_481890, baseEnd_481890] using wordTrace_append hprefix tailTrace_481890
  have hstable : (prefixWord ++ tailWord_481890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481890).length < 2 ^ (prefixWord ++ tailWord_481890).sum := by decide
  have hdescent : baseEnd_481890 < baseStart_481890 := by decide
  rcases family_descends (prefixWord ++ tailWord_481890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481898 : List Nat := [3, 1, 3, 2, 1, 1, 3, 1, 6]
def baseStart_481898 : Nat := 118140960795 + 481898 * 2 ^ 59
def prefixEnd_481898 : Nat := 4983230072969 + 3 ^ 40 * 481898 * 2
def baseEnd_481898 : Nat := 109975689084649246915021

theorem tailTrace_481898 : CollatzResearch.WordTrace tailWord_481898 prefixEnd_481898 109975689084649246915021 := by
  unfold tailWord_481898
  simp only [CollatzResearch.WordTrace]
  refine ⟨4394066002043330617785587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11717509338782214980761565 4394066002043330617785587)
  ·
    refine ⟨6591099003064995926678381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4394066002043330617785587 6591099003064995926678381)
    ·
      refine ⟨2471662126149373472504393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6591099003064995926678381 2471662126149373472504393)
      ·
        refine ⟨1853746594612030104378295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2471662126149373472504393 1853746594612030104378295)
        ·
          refine ⟨2780619891918045156567443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1853746594612030104378295 2780619891918045156567443)
          ·
            refine ⟨4170929837877067734851165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2780619891918045156567443 4170929837877067734851165)
            ·
              refine ⟨1564098689203900400569187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4170929837877067734851165 1564098689203900400569187)
              ·
                refine ⟨2346148033805850600853781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1564098689203900400569187 2346148033805850600853781)
                ·
                  refine ⟨109975689084649246915021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2346148033805850600853781 109975689084649246915021)
                  ·
                    rfl

theorem cell21_481898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_481898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_481898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_481898 prefixEnd_481898 := by exact prefixLift 481898
  have htrace : WordTrace (prefixWord ++ tailWord_481898) baseStart_481898 baseEnd_481898 := by
    simpa [prefixWord, tailWord_481898, baseEnd_481898] using wordTrace_append hprefix tailTrace_481898
  have hstable : (prefixWord ++ tailWord_481898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481898).length < 2 ^ (prefixWord ++ tailWord_481898).sum := by decide
  have hdescent : baseEnd_481898 < baseStart_481898 := by decide
  rcases family_descends (prefixWord ++ tailWord_481898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481901 : List Nat := [1, 5, 1, 1, 3, 1, 2, 4, 3]
def baseStart_481901 : Nat := 118140960795 + 481901 * 2 ^ 59
def prefixEnd_481901 : Nat := 4983230072969 + 3 ^ 40 * 481901 * 2
def baseEnd_481901 : Nat := 109976373725521908365015

theorem tailTrace_481901 : CollatzResearch.WordTrace tailWord_481901 prefixEnd_481901 109976373725521908365015 := by
  unfold tailWord_481901
  simp only [CollatzResearch.WordTrace]
  refine ⟨17576373427162453983501557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11717582284774969322334371 17576373427162453983501557)
  ·
    refine ⟨1647785008796480060953271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17576373427162453983501557 1647785008796480060953271)
    ·
      refine ⟨2471677513194720091429907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1647785008796480060953271 2471677513194720091429907)
      ·
        refine ⟨3707516269792080137144861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2471677513194720091429907 3707516269792080137144861)
        ·
          refine ⟨1390318601172030051429323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3707516269792080137144861 1390318601172030051429323)
          ·
            refine ⟨2085477901758045077143985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1390318601172030051429323 2085477901758045077143985)
            ·
              refine ⟨1564108426318533807857989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2085477901758045077143985 1564108426318533807857989)
              ·
                refine ⟨293270329934725088973373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1564108426318533807857989 293270329934725088973373)
                ·
                  refine ⟨109976373725521908365015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 293270329934725088973373 109976373725521908365015)
                  ·
                    rfl

theorem cell21_481901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_481901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_481901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_481901 prefixEnd_481901 := by exact prefixLift 481901
  have htrace : WordTrace (prefixWord ++ tailWord_481901) baseStart_481901 baseEnd_481901 := by
    simpa [prefixWord, tailWord_481901, baseEnd_481901] using wordTrace_append hprefix tailTrace_481901
  have hstable : (prefixWord ++ tailWord_481901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481901).length < 2 ^ (prefixWord ++ tailWord_481901).sum := by decide
  have hdescent : baseEnd_481901 < baseStart_481901 := by decide
  rcases family_descends (prefixWord ++ tailWord_481901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481946 : List Nat := [3, 1, 1, 6, 1, 2, 7]
def baseStart_481946 : Nat := 118140960795 + 481946 * 2 ^ 59
def prefixEnd_481946 : Nat := 4983230072969 + 3 ^ 40 * 481946 * 2
def baseEnd_481946 : Nat := 12220738148734647790547

theorem tailTrace_481946 : CollatzResearch.WordTrace tailWord_481946 prefixEnd_481946 12220738148734647790547 := by
  unfold tailWord_481946
  simp only [CollatzResearch.WordTrace]
  refine ⟨4394503677999856667222423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11718676474666284445926461 4394503677999856667222423)
  ·
    refine ⟨6591755516999785000833635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4394503677999856667222423 6591755516999785000833635)
    ·
      refine ⟨9887633275499677501250453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6591755516999785000833635 9887633275499677501250453)
      ·
        refine ⟨463482809789047382871115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9887633275499677501250453 463482809789047382871115)
        ·
          refine ⟨695224214683571074306673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463482809789047382871115 695224214683571074306673)
          ·
            refine ⟨521418161012678305730005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 695224214683571074306673 521418161012678305730005)
            ·
              refine ⟨12220738148734647790547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 521418161012678305730005 12220738148734647790547)
              ·
                rfl

theorem cell21_481946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 7].length) (baseStart_481946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_481946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_481946 prefixEnd_481946 := by exact prefixLift 481946
  have htrace : WordTrace (prefixWord ++ tailWord_481946) baseStart_481946 baseEnd_481946 := by
    simpa [prefixWord, tailWord_481946, baseEnd_481946] using wordTrace_append hprefix tailTrace_481946
  have hstable : (prefixWord ++ tailWord_481946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481946).length < 2 ^ (prefixWord ++ tailWord_481946).sum := by decide
  have hdescent : baseEnd_481946 < baseStart_481946 := by decide
  rcases family_descends (prefixWord ++ tailWord_481946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482005 : List Nat := [1, 3, 2, 5, 1, 9]
def baseStart_482005 : Nat := 118140960795 + 482005 * 2 ^ 59
def prefixEnd_482005 : Nat := 4983230072969 + 3 ^ 40 * 482005 * 2
def baseEnd_482005 : Nat := 4074078071942253282647

theorem tailTrace_482005 : CollatzResearch.WordTrace tailWord_482005 prefixEnd_482005 4074078071942253282647 := by
  unfold tailWord_482005
  simp only [CollatzResearch.WordTrace]
  refine ⟨17580166618785679745287469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11720111079190453163524979 17580166618785679745287469)
  ·
    refine ⟨6592562482044629904482801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17580166618785679745287469 6592562482044629904482801)
    ·
      refine ⟨4944421861533472428362101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6592562482044629904482801 4944421861533472428362101)
      ·
        refine ⟨463539549518763040158947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4944421861533472428362101 463539549518763040158947)
        ·
          refine ⟨695309324278144560238421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463539549518763040158947 695309324278144560238421)
          ·
            refine ⟨4074078071942253282647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 695309324278144560238421 4074078071942253282647)
            ·
              rfl

theorem cell21_482005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 9].length) (baseStart_482005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_482005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_482005 prefixEnd_482005 := by exact prefixLift 482005
  have htrace : WordTrace (prefixWord ++ tailWord_482005) baseStart_482005 baseEnd_482005 := by
    simpa [prefixWord, tailWord_482005, baseEnd_482005] using wordTrace_append hprefix tailTrace_482005
  have hstable : (prefixWord ++ tailWord_482005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482005).length < 2 ^ (prefixWord ++ tailWord_482005).sum := by decide
  have hdescent : baseEnd_482005 < baseStart_482005 := by decide
  rcases family_descends (prefixWord ++ tailWord_482005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482084 : List Nat := [2, 3, 1, 3, 3, 1, 3, 1, 4]
def baseStart_482084 : Nat := 118140960795 + 482084 * 2 ^ 59
def prefixEnd_482084 : Nat := 4983230072969 + 3 ^ 40 * 482084 * 2
def baseEnd_482084 : Nat := 110018136818754256814641

theorem tailTrace_482084 : CollatzResearch.WordTrace tailWord_482084 prefixEnd_482084 110018136818754256814641 := by
  unfold tailWord_482084
  simp only [CollatzResearch.WordTrace]
  refine ⟨8791523992749738118706653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11722031990332984158275537 8791523992749738118706653)
  ·
    refine ⟨3296821497281151794514995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8791523992749738118706653 3296821497281151794514995)
    ·
      refine ⟨4945232245921727691772493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3296821497281151794514995 4945232245921727691772493)
      ·
        refine ⟨1854462092220647884414685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4945232245921727691772493 1854462092220647884414685)
        ·
          refine ⟨695423284582742956655507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1854462092220647884414685 695423284582742956655507)
          ·
            refine ⟨1043134926874114434983261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 695423284582742956655507 1043134926874114434983261)
            ·
              refine ⟨391175597577792913118723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1043134926874114434983261 391175597577792913118723)
              ·
                refine ⟨586763396366689369678085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 391175597577792913118723 586763396366689369678085)
                ·
                  refine ⟨110018136818754256814641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 586763396366689369678085 110018136818754256814641)
                  ·
                    rfl

theorem cell21_482084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_482084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_482084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_482084 prefixEnd_482084 := by exact prefixLift 482084
  have htrace : WordTrace (prefixWord ++ tailWord_482084) baseStart_482084 baseEnd_482084 := by
    simpa [prefixWord, tailWord_482084, baseEnd_482084] using wordTrace_append hprefix tailTrace_482084
  have hstable : (prefixWord ++ tailWord_482084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482084).length < 2 ^ (prefixWord ++ tailWord_482084).sum := by decide
  have hdescent : baseEnd_482084 < baseStart_482084 := by decide
  rcases family_descends (prefixWord ++ tailWord_482084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482129 : List Nat := [1, 2, 2, 1, 7, 1, 1, 1, 5]
def baseStart_482129 : Nat := 118140960795 + 482129 * 2 ^ 59
def prefixEnd_482129 : Nat := 4983230072969 + 3 ^ 40 * 482129 * 2
def baseEnd_482129 : Nat := 110028406431844178564549

theorem tailTrace_482129 : CollatzResearch.WordTrace tailWord_482129 prefixEnd_482129 110028406431844178564549 := by
  unfold tailWord_482129
  simp only [CollatzResearch.WordTrace]
  refine ⟨17584689270336448922801441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11723126180224299281867627 17584689270336448922801441)
  ·
    refine ⟨13188516952752336692101081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17584689270336448922801441 13188516952752336692101081)
    ·
      refine ⟨9891387714564252519075811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13188516952752336692101081 9891387714564252519075811)
      ·
        refine ⟨14837081571846378778613717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9891387714564252519075811 14837081571846378778613717)
        ·
          refine ⟨347744099340149502623759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 14837081571846378778613717 347744099340149502623759)
          ·
            refine ⟨521616149010224253935639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347744099340149502623759 521616149010224253935639)
            ·
              refine ⟨782424223515336380903459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521616149010224253935639 782424223515336380903459)
              ·
                refine ⟨1173636335273004571355189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 782424223515336380903459 1173636335273004571355189)
                ·
                  refine ⟨110028406431844178564549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1173636335273004571355189 110028406431844178564549)
                  ·
                    rfl

theorem cell21_482129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 5].length) (baseStart_482129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_482129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_482129 prefixEnd_482129 := by exact prefixLift 482129
  have htrace : WordTrace (prefixWord ++ tailWord_482129) baseStart_482129 baseEnd_482129 := by
    simpa [prefixWord, tailWord_482129, baseEnd_482129] using wordTrace_append hprefix tailTrace_482129
  have hstable : (prefixWord ++ tailWord_482129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482129).length < 2 ^ (prefixWord ++ tailWord_482129).sum := by decide
  have hdescent : baseEnd_482129 < baseStart_482129 := by decide
  rcases family_descends (prefixWord ++ tailWord_482129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482174 : List Nat := [4, 2, 3, 1, 3, 8]
def baseStart_482174 : Nat := 118140960795 + 482174 * 2 ^ 59
def prefixEnd_482174 : Nat := 4983230072969 + 3 ^ 40 * 482174 * 2
def baseEnd_482174 : Nat := 4075506520182744456091

theorem tailTrace_482174 : CollatzResearch.WordTrace tailWord_482174 prefixEnd_482174 4075506520182744456091 := by
  unfold tailWord_482174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2198291319396677701023697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11724220370115614405459717 2198291319396677701023697)
  ·
    refine ⟨1648718489547508275767773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2198291319396677701023697 1648718489547508275767773)
    ·
      refine ⟨618269433580315603412915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1648718489547508275767773 618269433580315603412915)
      ·
        refine ⟨927404150370473405119373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618269433580315603412915 927404150370473405119373)
        ·
          refine ⟨347776556388927526919765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 927404150370473405119373 347776556388927526919765)
          ·
            refine ⟨4075506520182744456091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 347776556388927526919765 4075506520182744456091)
            ·
              rfl

theorem cell21_482174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 8].length) (baseStart_482174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_482174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_482174 prefixEnd_482174 := by exact prefixLift 482174
  have htrace : WordTrace (prefixWord ++ tailWord_482174) baseStart_482174 baseEnd_482174 := by
    simpa [prefixWord, tailWord_482174, baseEnd_482174] using wordTrace_append hprefix tailTrace_482174
  have hstable : (prefixWord ++ tailWord_482174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482174).length < 2 ^ (prefixWord ++ tailWord_482174).sum := by decide
  have hdescent : baseEnd_482174 < baseStart_482174 := by decide
  rcases family_descends (prefixWord ++ tailWord_482174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482354 : List Nat := [3, 2, 1, 1, 2, 2, 4, 2, 4]
def baseStart_482354 : Nat := 118140960795 + 482354 * 2 ^ 59
def prefixEnd_482354 : Nat := 4983230072969 + 3 ^ 40 * 482354 * 2
def baseEnd_482354 : Nat := 110079754497293787314089

theorem tailTrace_482354 : CollatzResearch.WordTrace tailWord_482354 prefixEnd_482354 110079754497293787314089 := by
  unfold tailWord_482354
  simp only [CollatzResearch.WordTrace]
  refine ⟨4398223923630328087435529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11728597129680874899828077 4398223923630328087435529)
  ·
    refine ⟨3298667942722746065576647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4398223923630328087435529 3298667942722746065576647)
    ·
      refine ⟨4948001914084119098364971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3298667942722746065576647 4948001914084119098364971)
      ·
        refine ⟨7422002871126178647547457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4948001914084119098364971 7422002871126178647547457)
        ·
          refine ⟨5566502153344633985660593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7422002871126178647547457 5566502153344633985660593)
          ·
            refine ⟨4174876615008475489245445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5566502153344633985660593 4174876615008475489245445)
            ·
              refine ⟨782789365314089154233521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4174876615008475489245445 782789365314089154233521)
              ·
                refine ⟨587092023985566865675141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 782789365314089154233521 587092023985566865675141)
                ·
                  refine ⟨110079754497293787314089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 587092023985566865675141 110079754497293787314089)
                  ·
                    rfl

theorem cell21_482354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_482354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_482354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_482354 prefixEnd_482354 := by exact prefixLift 482354
  have htrace : WordTrace (prefixWord ++ tailWord_482354) baseStart_482354 baseEnd_482354 := by
    simpa [prefixWord, tailWord_482354, baseEnd_482354] using wordTrace_append hprefix tailTrace_482354
  have hstable : (prefixWord ++ tailWord_482354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482354).length < 2 ^ (prefixWord ++ tailWord_482354).sum := by decide
  have hdescent : baseEnd_482354 < baseStart_482354 := by decide
  rcases family_descends (prefixWord ++ tailWord_482354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482520 : List Nat := [2, 1, 2, 2, 6, 8]
def baseStart_482520 : Nat := 118140960795 + 482520 * 2 ^ 59
def prefixEnd_482520 : Nat := 4983230072969 + 3 ^ 40 * 482520 * 2
def baseEnd_482520 : Nat := 4078431035515347686929

theorem tailTrace_482520 : CollatzResearch.WordTrace tailWord_482520 prefixEnd_482520 4078431035515347686929 := by
  unfold tailWord_482520
  simp only [CollatzResearch.WordTrace]
  refine ⟨8799475105959961350142507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11732633474613281800190009 8799475105959961350142507)
  ·
    refine ⟨13199212658939942025213761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8799475105959961350142507 13199212658939942025213761)
    ·
      refine ⟨9899409494204956518910321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13199212658939942025213761 9899409494204956518910321)
      ·
        refine ⟨7424557120653717389182741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9899409494204956518910321 7424557120653717389182741)
        ·
          refine ⟨348026115030643002617941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7424557120653717389182741 348026115030643002617941)
          ·
            refine ⟨4078431035515347686929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 348026115030643002617941 4078431035515347686929)
            ·
              rfl

theorem cell21_482520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 8].length) (baseStart_482520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_482520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_482520 prefixEnd_482520 := by exact prefixLift 482520
  have htrace : WordTrace (prefixWord ++ tailWord_482520) baseStart_482520 baseEnd_482520 := by
    simpa [prefixWord, tailWord_482520, baseEnd_482520] using wordTrace_append hprefix tailTrace_482520
  have hstable : (prefixWord ++ tailWord_482520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482520).length < 2 ^ (prefixWord ++ tailWord_482520).sum := by decide
  have hdescent : baseEnd_482520 < baseStart_482520 := by decide
  rcases family_descends (prefixWord ++ tailWord_482520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482613 : List Nat := [1, 3, 3, 1, 2, 4, 2, 5]
def baseStart_482613 : Nat := 118140960795 + 482613 * 2 ^ 59
def prefixEnd_482613 : Nat := 4983230072969 + 3 ^ 40 * 482613 * 2
def baseEnd_482613 : Nat := 36712953941988964165631

theorem tailTrace_482613 : CollatzResearch.WordTrace tailWord_482613 prefixEnd_482613 36712953941988964165631 := by
  unfold tailWord_482613
  simp only [CollatzResearch.WordTrace]
  refine ⟨17602342200582999583420493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11734894800388666388946995 17602342200582999583420493)
  ·
    refine ⟨6600878325218624843782685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17602342200582999583420493 6600878325218624843782685)
    ·
      refine ⟨2475329371956984316418507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6600878325218624843782685 2475329371956984316418507)
      ·
        refine ⟨3712994057935476474627761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2475329371956984316418507 3712994057935476474627761)
        ·
          refine ⟨2784745543451607355970821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3712994057935476474627761 2784745543451607355970821)
          ·
            refine ⟨522139789397176379244529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2784745543451607355970821 522139789397176379244529)
            ·
              refine ⟨391604842047882284433397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 522139789397176379244529 391604842047882284433397)
              ·
                refine ⟨36712953941988964165631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 391604842047882284433397 36712953941988964165631)
                ·
                  rfl

theorem cell21_482613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 5].length) (baseStart_482613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_482613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_482613 prefixEnd_482613 := by exact prefixLift 482613
  have htrace : WordTrace (prefixWord ++ tailWord_482613) baseStart_482613 baseEnd_482613 := by
    simpa [prefixWord, tailWord_482613, baseEnd_482613] using wordTrace_append hprefix tailTrace_482613
  have hstable : (prefixWord ++ tailWord_482613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482613).length < 2 ^ (prefixWord ++ tailWord_482613).sum := by decide
  have hdescent : baseEnd_482613 < baseStart_482613 := by decide
  rcases family_descends (prefixWord ++ tailWord_482613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482624 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 8]
def baseStart_482624 : Nat := 118140960795 + 482624 * 2 ^ 59
def prefixEnd_482624 : Nat := 4983230072969 + 3 ^ 40 * 482624 * 2
def baseEnd_482624 : Nat := 110141372175833317813537

theorem tailTrace_482624 : CollatzResearch.WordTrace tailWord_482624 prefixEnd_482624 110141372175833317813537 := by
  unfold tailWord_482624
  simp only [CollatzResearch.WordTrace]
  refine ⟨8801371701771574231035463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11735162269028765641380617 8801371701771574231035463)
  ·
    refine ⟨13202057552657361346553195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8801371701771574231035463 13202057552657361346553195)
    ·
      refine ⟨19803086328986042019829793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13202057552657361346553195 19803086328986042019829793)
      ·
        refine ⟨14852314746739531514872345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19803086328986042019829793 14852314746739531514872345)
        ·
          refine ⟨11139236060054648636154259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14852314746739531514872345 11139236060054648636154259)
          ·
            refine ⟨16708854090081972954231389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11139236060054648636154259 16708854090081972954231389)
            ·
              refine ⟨6265820283780739857836771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16708854090081972954231389 6265820283780739857836771)
              ·
                refine ⟨9398730425671109786755157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6265820283780739857836771 9398730425671109786755157)
                ·
                  refine ⟨110141372175833317813537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9398730425671109786755157 110141372175833317813537)
                  ·
                    rfl

theorem cell21_482624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 8].length) (baseStart_482624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_482624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_482624 prefixEnd_482624 := by exact prefixLift 482624
  have htrace : WordTrace (prefixWord ++ tailWord_482624) baseStart_482624 baseEnd_482624 := by
    simpa [prefixWord, tailWord_482624, baseEnd_482624] using wordTrace_append hprefix tailTrace_482624
  have hstable : (prefixWord ++ tailWord_482624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482624).length < 2 ^ (prefixWord ++ tailWord_482624).sum := by decide
  have hdescent : baseEnd_482624 < baseStart_482624 := by decide
  rcases family_descends (prefixWord ++ tailWord_482624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482641 : List Nat := [1, 2, 2, 1, 4, 1, 2, 4, 4]
def baseStart_482641 : Nat := 118140960795 + 482641 * 2 ^ 59
def prefixEnd_482641 : Nat := 4983230072969 + 3 ^ 40 * 482641 * 2
def baseEnd_482641 : Nat := 110145251807445066030169

theorem tailTrace_482641 : CollatzResearch.WordTrace tailWord_482641 prefixEnd_482641 110145251807445066030169 := by
  unfold tailWord_482641
  simp only [CollatzResearch.WordTrace]
  refine ⟨17603363444481560365439777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11735575629654373576959851 17603363444481560365439777)
  ·
    refine ⟨13202522583361170274079833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17603363444481560365439777 13202522583361170274079833)
    ·
      refine ⟨9901891937520877705559875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13202522583361170274079833 9901891937520877705559875)
      ·
        refine ⟨14852837906281316558339813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9901891937520877705559875 14852837906281316558339813)
        ·
          refine ⟨2784907107427746854688715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14852837906281316558339813 2784907107427746854688715)
          ·
            refine ⟨4177360661141620282033073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2784907107427746854688715 4177360661141620282033073)
            ·
              refine ⟨3133020495856215211524805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4177360661141620282033073 3133020495856215211524805)
              ·
                refine ⟨587441342973040352160901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3133020495856215211524805 587441342973040352160901)
                ·
                  refine ⟨110145251807445066030169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 587441342973040352160901 110145251807445066030169)
                  ·
                    rfl

theorem cell21_482641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 4].length) (baseStart_482641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_482641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_482641 prefixEnd_482641 := by exact prefixLift 482641
  have htrace : WordTrace (prefixWord ++ tailWord_482641) baseStart_482641 baseEnd_482641 := by
    simpa [prefixWord, tailWord_482641, baseEnd_482641] using wordTrace_append hprefix tailTrace_482641
  have hstable : (prefixWord ++ tailWord_482641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482641).length < 2 ^ (prefixWord ++ tailWord_482641).sum := by decide
  have hdescent : baseEnd_482641 < baseStart_482641 := by decide
  rcases family_descends (prefixWord ++ tailWord_482641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482658 : List Nat := [3, 3, 2, 1, 1, 1, 3, 3, 4]
def baseStart_482658 : Nat := 118140960795 + 482658 * 2 ^ 59
def prefixEnd_482658 : Nat := 4983230072969 + 3 ^ 40 * 482658 * 2
def baseEnd_482658 : Nat := 110149131439056814246801

theorem tailTrace_482658 : CollatzResearch.WordTrace tailWord_482658 prefixEnd_482658 110149131439056814246801 := by
  unfold tailWord_482658
  simp only [CollatzResearch.WordTrace]
  refine ⟨4400995871354993067202157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11735988990279981512539085 4400995871354993067202157)
  ·
    refine ⟨1650373451758122400200809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4400995871354993067202157 1650373451758122400200809)
    ·
      refine ⟨1237780088818591800150607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1650373451758122400200809 1237780088818591800150607)
      ·
        refine ⟨1856670133227887700225911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1237780088818591800150607 1856670133227887700225911)
        ·
          refine ⟨2785005199841831550338867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1856670133227887700225911 2785005199841831550338867)
          ·
            refine ⟨4177507799762747325508301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2785005199841831550338867 4177507799762747325508301)
            ·
              refine ⟨1566565424911030247065613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4177507799762747325508301 1566565424911030247065613)
              ·
                refine ⟨587462034341636342649605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1566565424911030247065613 587462034341636342649605)
                ·
                  refine ⟨110149131439056814246801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 587462034341636342649605 110149131439056814246801)
                  ·
                    rfl

theorem cell21_482658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_482658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_482658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_482658 prefixEnd_482658 := by exact prefixLift 482658
  have htrace : WordTrace (prefixWord ++ tailWord_482658) baseStart_482658 baseEnd_482658 := by
    simpa [prefixWord, tailWord_482658, baseEnd_482658] using wordTrace_append hprefix tailTrace_482658
  have hstable : (prefixWord ++ tailWord_482658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482658).length < 2 ^ (prefixWord ++ tailWord_482658).sum := by decide
  have hdescent : baseEnd_482658 < baseStart_482658 := by decide
  rcases family_descends (prefixWord ++ tailWord_482658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482706 : List Nat := [3, 2, 3, 3, 1, 2, 1, 6]
def baseStart_482706 : Nat := 118140960795 + 482706 * 2 ^ 59
def prefixEnd_482706 : Nat := 4983230072969 + 3 ^ 40 * 482706 * 2
def baseEnd_482706 : Nat := 36720028564339799148901

theorem tailTrace_482706 : CollatzResearch.WordTrace tailWord_482706 prefixEnd_482706 36720028564339799148901 := by
  unfold tailWord_482706
  simp only [CollatzResearch.WordTrace]
  refine ⟨4401433547311519116638993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11737156126164050977703981 4401433547311519116638993)
  ·
    refine ⟨3301075160483639337479245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4401433547311519116638993 3301075160483639337479245)
    ·
      refine ⟨1237903185181364751554717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3301075160483639337479245 1237903185181364751554717)
      ·
        refine ⟨464213694443011781833019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1237903185181364751554717 464213694443011781833019)
        ·
          refine ⟨696320541664517672749529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464213694443011781833019 696320541664517672749529)
          ·
            refine ⟨522240406248388254562147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 696320541664517672749529 522240406248388254562147)
            ·
              refine ⟨783360609372582381843221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522240406248388254562147 783360609372582381843221)
              ·
                refine ⟨36720028564339799148901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 783360609372582381843221 36720028564339799148901)
                ·
                  rfl

theorem cell21_482706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 6].length) (baseStart_482706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_482706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_482706 prefixEnd_482706 := by exact prefixLift 482706
  have htrace : WordTrace (prefixWord ++ tailWord_482706) baseStart_482706 baseEnd_482706 := by
    simpa [prefixWord, tailWord_482706, baseEnd_482706] using wordTrace_append hprefix tailTrace_482706
  have hstable : (prefixWord ++ tailWord_482706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482706).length < 2 ^ (prefixWord ++ tailWord_482706).sum := by decide
  have hdescent : baseEnd_482706 < baseStart_482706 := by decide
  rcases family_descends (prefixWord ++ tailWord_482706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482748 : List Nat := [2, 2, 2, 4, 2, 1, 8]
def baseStart_482748 : Nat := 118140960795 + 482748 * 2 ^ 59
def prefixEnd_482748 : Nat := 4983230072969 + 3 ^ 40 * 482748 * 2
def baseEnd_482748 : Nat := 12241074518359628638513

theorem tailTrace_482748 : CollatzResearch.WordTrace tailWord_482748 prefixEnd_482748 12241074518359628638513 := by
  unfold tailWord_482748
  simp only [CollatzResearch.WordTrace]
  refine ⟨8803633027546958819792449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11738177370062611759723265 8803633027546958819792449)
  ·
    refine ⟨6602724770660219114844337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8803633027546958819792449 6602724770660219114844337)
    ·
      refine ⟨4952043577995164336133253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6602724770660219114844337 4952043577995164336133253)
      ·
        refine ⟨928508170874093313024985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4952043577995164336133253 928508170874093313024985)
        ·
          refine ⟨696381128155569984768739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 928508170874093313024985 696381128155569984768739)
          ·
            refine ⟨1044571692233354977153109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 696381128155569984768739 1044571692233354977153109)
            ·
              refine ⟨12241074518359628638513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1044571692233354977153109 12241074518359628638513)
              ·
                rfl

theorem cell21_482748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 8].length) (baseStart_482748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_482748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_482748 prefixEnd_482748 := by exact prefixLift 482748
  have htrace : WordTrace (prefixWord ++ tailWord_482748) baseStart_482748 baseEnd_482748 := by
    simpa [prefixWord, tailWord_482748, baseEnd_482748] using wordTrace_append hprefix tailTrace_482748
  have hstable : (prefixWord ++ tailWord_482748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482748).length < 2 ^ (prefixWord ++ tailWord_482748).sum := by decide
  have hdescent : baseEnd_482748 < baseStart_482748 := by decide
  rcases family_descends (prefixWord ++ tailWord_482748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482762 : List Nat := [3, 1, 2, 1, 2, 3, 1, 3, 5]
def baseStart_482762 : Nat := 118140960795 + 482762 * 2 ^ 59
def prefixEnd_482762 : Nat := 4983230072969 + 3 ^ 40 * 482762 * 2
def baseEnd_482762 : Nat := 110172865655975744513255

theorem tailTrace_482762 : CollatzResearch.WordTrace tailWord_482762 prefixEnd_482762 110172865655975744513255 := by
  unfold tailWord_482762
  simp only [CollatzResearch.WordTrace]
  refine ⟨4401944169260799507648635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11738517784695465353729693 4401944169260799507648635)
  ·
    refine ⟨6602916253891199261472953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4401944169260799507648635 6602916253891199261472953)
    ·
      refine ⟨4952187190418399446104715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6602916253891199261472953 4952187190418399446104715)
      ·
        refine ⟨7428280785627599169157073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4952187190418399446104715 7428280785627599169157073)
        ·
          refine ⟨5571210589220699376867805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7428280785627599169157073 5571210589220699376867805)
          ·
            refine ⟨2089203970957762266325427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5571210589220699376867805 2089203970957762266325427)
            ·
              refine ⟨3133805956436643399488141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2089203970957762266325427 3133805956436643399488141)
              ·
                refine ⟨1175177233663741274808053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3133805956436643399488141 1175177233663741274808053)
                ·
                  refine ⟨110172865655975744513255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1175177233663741274808053 110172865655975744513255)
                  ·
                    rfl

theorem cell21_482762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_482762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_482762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_482762 prefixEnd_482762 := by exact prefixLift 482762
  have htrace : WordTrace (prefixWord ++ tailWord_482762) baseStart_482762 baseEnd_482762 := by
    simpa [prefixWord, tailWord_482762, baseEnd_482762] using wordTrace_append hprefix tailTrace_482762
  have hstable : (prefixWord ++ tailWord_482762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482762).length < 2 ^ (prefixWord ++ tailWord_482762).sum := by decide
  have hdescent : baseEnd_482762 < baseStart_482762 := by decide
  rcases family_descends (prefixWord ++ tailWord_482762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482827 : List Nat := [1, 1, 1, 1, 8, 2, 2, 1, 4]
def baseStart_482827 : Nat := 118140960795 + 482827 * 2 ^ 59
def prefixEnd_482827 : Nat := 4983230072969 + 3 ^ 40 * 482827 * 2
def baseEnd_482827 : Nat := 110187699541550075929789

theorem tailTrace_482827 : CollatzResearch.WordTrace tailWord_482827 prefixEnd_482827 110187699541550075929789 := by
  unfold tailWord_482827
  simp only [CollatzResearch.WordTrace]
  refine ⟨17610147421807714131710735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11740098281205142754473823 17610147421807714131710735)
  ·
    refine ⟨26415221132711571197566103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17610147421807714131710735 26415221132711571197566103)
    ·
      refine ⟨39622831699067356796349155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26415221132711571197566103 39622831699067356796349155)
      ·
        refine ⟨59434247548601035194523733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39622831699067356796349155 59434247548601035194523733)
        ·
          refine ⟨696495088460168381185825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 59434247548601035194523733 696495088460168381185825)
          ·
            refine ⟨522371316345126285889369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 696495088460168381185825 522371316345126285889369)
            ·
              refine ⟨391778487258844714417027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 522371316345126285889369 391778487258844714417027)
              ·
                refine ⟨587667730888267071625541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 391778487258844714417027 587667730888267071625541)
                ·
                  refine ⟨110187699541550075929789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 587667730888267071625541 110187699541550075929789)
                  ·
                    rfl

theorem cell21_482827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 4].length) (baseStart_482827 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_482827 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_482827 prefixEnd_482827 := by exact prefixLift 482827
  have htrace : WordTrace (prefixWord ++ tailWord_482827) baseStart_482827 baseEnd_482827 := by
    simpa [prefixWord, tailWord_482827, baseEnd_482827] using wordTrace_append hprefix tailTrace_482827
  have hstable : (prefixWord ++ tailWord_482827).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482827).length < 2 ^ (prefixWord ++ tailWord_482827).sum := by decide
  have hdescent : baseEnd_482827 < baseStart_482827 := by decide
  rcases family_descends (prefixWord ++ tailWord_482827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482869 : List Nat := [1, 3, 3, 1, 1, 3, 1, 4, 4]
def baseStart_482869 : Nat := 118140960795 + 482869 * 2 ^ 59
def prefixEnd_482869 : Nat := 4983230072969 + 3 ^ 40 * 482869 * 2
def baseEnd_482869 : Nat := 110197284513767336229703

theorem tailTrace_482869 : CollatzResearch.WordTrace tailWord_482869 prefixEnd_482869 110197284513767336229703 := by
  unfold tailWord_482869
  simp only [CollatzResearch.WordTrace]
  refine ⟨17611679287655555304739661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11741119525103703536493107 17611679287655555304739661)
  ·
    refine ⟨6604379732870833239277373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17611679287655555304739661 6604379732870833239277373)
    ·
      refine ⟨2476642399826562464729015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6604379732870833239277373 2476642399826562464729015)
      ·
        refine ⟨3714963599739843697093523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2476642399826562464729015 3714963599739843697093523)
        ·
          refine ⟨5572445399609765545640285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3714963599739843697093523 5572445399609765545640285)
          ·
            refine ⟨2089667024853662079615107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5572445399609765545640285 2089667024853662079615107)
            ·
              refine ⟨3134500537280493119422661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2089667024853662079615107 3134500537280493119422661)
              ·
                refine ⟨587718850740092459891749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3134500537280493119422661 587718850740092459891749)
                ·
                  refine ⟨110197284513767336229703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 587718850740092459891749 110197284513767336229703)
                  ·
                    rfl

theorem cell21_482869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_482869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_482869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_482869 prefixEnd_482869 := by exact prefixLift 482869
  have htrace : WordTrace (prefixWord ++ tailWord_482869) baseStart_482869 baseEnd_482869 := by
    simpa [prefixWord, tailWord_482869, baseEnd_482869] using wordTrace_append hprefix tailTrace_482869
  have hstable : (prefixWord ++ tailWord_482869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482869).length < 2 ^ (prefixWord ++ tailWord_482869).sum := by decide
  have hdescent : baseEnd_482869 < baseStart_482869 := by decide
  rcases family_descends (prefixWord ++ tailWord_482869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482872 : List Nat := [2, 1, 2, 1, 4, 2, 4, 2, 3]
def baseStart_482872 : Nat := 118140960795 + 482872 * 2 ^ 59
def prefixEnd_482872 : Nat := 4983230072969 + 3 ^ 40 * 482872 * 2
def baseEnd_482872 : Nat := 110197969154639997679697

theorem tailTrace_482872 : CollatzResearch.WordTrace tailWord_482872 prefixEnd_482872 110197969154639997679697 := by
  unfold tailWord_482872
  simp only [CollatzResearch.WordTrace]
  refine ⟨8805894353322343408549435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11741192471096457878065913 8805894353322343408549435)
  ·
    refine ⟨13208841529983515112824153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8805894353322343408549435 13208841529983515112824153)
    ·
      refine ⟨9906631147487636334618115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13208841529983515112824153 9906631147487636334618115)
      ·
        refine ⟨14859946721231454501927173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9906631147487636334618115 14859946721231454501927173)
        ·
          refine ⟨2786240010230897719111345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14859946721231454501927173 2786240010230897719111345)
          ·
            refine ⟨2089680007673173289333509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2786240010230897719111345 2089680007673173289333509)
            ·
              refine ⟨391815001438719991750033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2089680007673173289333509 391815001438719991750033)
              ·
                refine ⟨293861251079039993812525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391815001438719991750033 293861251079039993812525)
                ·
                  refine ⟨110197969154639997679697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 293861251079039993812525 110197969154639997679697)
                  ·
                    rfl

theorem cell21_482872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 2, 3].length) (baseStart_482872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_482872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_482872 prefixEnd_482872 := by exact prefixLift 482872
  have htrace : WordTrace (prefixWord ++ tailWord_482872) baseStart_482872 baseEnd_482872 := by
    simpa [prefixWord, tailWord_482872, baseEnd_482872] using wordTrace_append hprefix tailTrace_482872
  have hstable : (prefixWord ++ tailWord_482872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482872).length < 2 ^ (prefixWord ++ tailWord_482872).sum := by decide
  have hdescent : baseEnd_482872 < baseStart_482872 := by decide
  rcases family_descends (prefixWord ++ tailWord_482872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482900 : List Nat := [2, 4, 1, 1, 1, 2, 5, 5]
def baseStart_482900 : Nat := 118140960795 + 482900 * 2 ^ 59
def prefixEnd_482900 : Nat := 4983230072969 + 3 ^ 40 * 482900 * 2
def baseEnd_482900 : Nat := 36734786378706057070991

theorem tailTrace_482900 : CollatzResearch.WordTrace tailWord_482900 prefixEnd_482900 36734786378706057070991 := by
  unfold tailWord_482900
  simp only [CollatzResearch.WordTrace]
  refine ⟨8806404975271623799559077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11741873300362165066078769 8806404975271623799559077)
  ·
    refine ⟨1651200932863429462417327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8806404975271623799559077 1651200932863429462417327)
    ·
      refine ⟨2476801399295144193625991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1651200932863429462417327 2476801399295144193625991)
      ·
        refine ⟨3715202098942716290438987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2476801399295144193625991 3715202098942716290438987)
        ·
          refine ⟨5572803148414074435658481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3715202098942716290438987 5572803148414074435658481)
          ·
            refine ⟨4179602361310555826743861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5572803148414074435658481 4179602361310555826743861)
            ·
              refine ⟨391837721372864608757237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4179602361310555826743861 391837721372864608757237)
              ·
                refine ⟨36734786378706057070991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 391837721372864608757237 36734786378706057070991)
                ·
                  rfl

theorem cell21_482900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 5].length) (baseStart_482900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_482900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_482900 prefixEnd_482900 := by exact prefixLift 482900
  have htrace : WordTrace (prefixWord ++ tailWord_482900) baseStart_482900 baseEnd_482900 := by
    simpa [prefixWord, tailWord_482900, baseEnd_482900] using wordTrace_append hprefix tailTrace_482900
  have hstable : (prefixWord ++ tailWord_482900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482900).length < 2 ^ (prefixWord ++ tailWord_482900).sum := by decide
  have hdescent : baseEnd_482900 < baseStart_482900 := by decide
  rcases family_descends (prefixWord ++ tailWord_482900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483041 : List Nat := [1, 2, 3, 1, 5, 2, 2, 2, 3]
def baseStart_483041 : Nat := 118140960795 + 483041 * 2 ^ 59
def prefixEnd_483041 : Nat := 4983230072969 + 3 ^ 40 * 483041 * 2
def baseEnd_483041 : Nat := 110236537257133259362685

theorem tailTrace_483041 : CollatzResearch.WordTrace tailWord_483041 prefixEnd_483041 110236537257133259362685 := by
  unfold tailWord_483041
  simp only [CollatzResearch.WordTrace]
  refine ⟨17617952643032428680000977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11745301762021619120000651 17617952643032428680000977)
  ·
    refine ⟨13213464482274321510000733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17617952643032428680000977 13213464482274321510000733)
    ·
      refine ⟨4955049180852870566250275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13213464482274321510000733 4955049180852870566250275)
      ·
        refine ⟨7432573771279305849375413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4955049180852870566250275 7432573771279305849375413)
        ·
          refine ⟨696803791057434923378945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7432573771279305849375413 696803791057434923378945)
          ·
            refine ⟨522602843293076192534209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 696803791057434923378945 522602843293076192534209)
            ·
              refine ⟨391952132469807144400657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 522602843293076192534209 391952132469807144400657)
              ·
                refine ⟨293964099352355358300493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391952132469807144400657 293964099352355358300493)
                ·
                  refine ⟨110236537257133259362685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 293964099352355358300493 110236537257133259362685)
                  ·
                    rfl

theorem cell21_483041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 2, 3].length) (baseStart_483041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_483041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_483041 prefixEnd_483041 := by exact prefixLift 483041
  have htrace : WordTrace (prefixWord ++ tailWord_483041) baseStart_483041 baseEnd_483041 := by
    simpa [prefixWord, tailWord_483041, baseEnd_483041] using wordTrace_append hprefix tailTrace_483041
  have hstable : (prefixWord ++ tailWord_483041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483041).length < 2 ^ (prefixWord ++ tailWord_483041).sum := by decide
  have hdescent : baseEnd_483041 < baseStart_483041 := by decide
  rcases family_descends (prefixWord ++ tailWord_483041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483049 : List Nat := [1, 2, 1, 1, 1, 2, 3, 5, 5]
def baseStart_483049 : Nat := 118140960795 + 483049 * 2 ^ 59
def prefixEnd_483049 : Nat := 4983230072969 + 3 ^ 40 * 483049 * 2
def baseEnd_483049 : Nat := 110238362966127023229335

theorem tailTrace_483049 : CollatzResearch.WordTrace tailWord_483049 prefixEnd_483049 110238362966127023229335 := by
  unfold tailWord_483049
  simp only [CollatzResearch.WordTrace]
  refine ⟨17618244427003446046292201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11745496284668964030861467 17618244427003446046292201)
  ·
    refine ⟨13213683320252584534719151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17618244427003446046292201 13213683320252584534719151)
    ·
      refine ⟨19820524980378876802078727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13213683320252584534719151 19820524980378876802078727)
      ·
        refine ⟨29730787470568315203118091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19820524980378876802078727 29730787470568315203118091)
        ·
          refine ⟨44596181205852472804677137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29730787470568315203118091 44596181205852472804677137)
          ·
            refine ⟨33447135904389354603507853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44596181205852472804677137 33447135904389354603507853)
            ·
              refine ⟨12542675964146007976315445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33447135904389354603507853 12542675964146007976315445)
              ·
                refine ⟨1175875871638688247779573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12542675964146007976315445 1175875871638688247779573)
                ·
                  refine ⟨110238362966127023229335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1175875871638688247779573 110238362966127023229335)
                  ·
                    rfl

theorem cell21_483049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 5].length) (baseStart_483049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_483049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_483049 prefixEnd_483049 := by exact prefixLift 483049
  have htrace : WordTrace (prefixWord ++ tailWord_483049) baseStart_483049 baseEnd_483049 := by
    simpa [prefixWord, tailWord_483049, baseEnd_483049] using wordTrace_append hprefix tailTrace_483049
  have hstable : (prefixWord ++ tailWord_483049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483049).length < 2 ^ (prefixWord ++ tailWord_483049).sum := by decide
  have hdescent : baseEnd_483049 < baseStart_483049 := by decide
  rcases family_descends (prefixWord ++ tailWord_483049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483080 : List Nat := [2, 1, 3, 2, 2, 1, 2, 2, 6]
def baseStart_483080 : Nat := 118140960795 + 483080 * 2 ^ 59
def prefixEnd_483080 : Nat := 4983230072969 + 3 ^ 40 * 483080 * 2
def baseEnd_483080 : Nat := 110245437588477858212605

theorem tailTrace_483080 : CollatzResearch.WordTrace tailWord_483080 prefixEnd_483080 110245437588477858212605 := by
  unfold tailWord_483080
  simp only [CollatzResearch.WordTrace]
  refine ⟨8809687544945569170335347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11746250059927425560447129 8809687544945569170335347)
  ·
    refine ⟨13214531317418353755503021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8809687544945569170335347 13214531317418353755503021)
    ·
      refine ⟨4955449244031882658313633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13214531317418353755503021 4955449244031882658313633)
      ·
        refine ⟨3716586933023911993735225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4955449244031882658313633 3716586933023911993735225)
        ·
          refine ⟨2787440199767933995301419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3716586933023911993735225 2787440199767933995301419)
          ·
            refine ⟨4181160299651900992952129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2787440199767933995301419 4181160299651900992952129)
            ·
              refine ⟨3135870224738925744714097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4181160299651900992952129 3135870224738925744714097)
              ·
                refine ⟨2351902668554194308535573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3135870224738925744714097 2351902668554194308535573)
                ·
                  refine ⟨110245437588477858212605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2351902668554194308535573 110245437588477858212605)
                  ·
                    rfl

theorem cell21_483080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 6].length) (baseStart_483080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_483080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_483080 prefixEnd_483080 := by exact prefixLift 483080
  have htrace : WordTrace (prefixWord ++ tailWord_483080) baseStart_483080 baseEnd_483080 := by
    simpa [prefixWord, tailWord_483080, baseEnd_483080] using wordTrace_append hprefix tailTrace_483080
  have hstable : (prefixWord ++ tailWord_483080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483080).length < 2 ^ (prefixWord ++ tailWord_483080).sum := by decide
  have hdescent : baseEnd_483080 < baseStart_483080 := by decide
  rcases family_descends (prefixWord ++ tailWord_483080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483128 : List Nat := [2, 1, 2, 1, 3, 5, 2, 5]
def baseStart_483128 : Nat := 118140960795 + 483128 * 2 ^ 59
def prefixEnd_483128 : Nat := 4983230072969 + 3 ^ 40 * 483128 * 2
def baseEnd_483128 : Nat := 36752130614146813804169

theorem tailTrace_483128 : CollatzResearch.WordTrace tailWord_483128 prefixEnd_483128 36752130614146813804169 := by
  unfold tailWord_483128
  simp only [CollatzResearch.WordTrace]
  refine ⟨8810562896858621269209019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11747417195811495025612025 8810562896858621269209019)
  ·
    refine ⟨13215844345287931903813529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8810562896858621269209019 13215844345287931903813529)
    ·
      refine ⟨9911883258965948927860147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13215844345287931903813529 9911883258965948927860147)
      ·
        refine ⟨14867824888448923391790221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9911883258965948927860147 14867824888448923391790221)
        ·
          refine ⟨5575434333168346271921333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14867824888448923391790221 5575434333168346271921333)
          ·
            refine ⟨522696968734532462992625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5575434333168346271921333 522696968734532462992625)
            ·
              refine ⟨392022726550899347244469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 522696968734532462992625 392022726550899347244469)
              ·
                refine ⟨36752130614146813804169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 392022726550899347244469 36752130614146813804169)
                ·
                  rfl

theorem cell21_483128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 5].length) (baseStart_483128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_483128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_483128 prefixEnd_483128 := by exact prefixLift 483128
  have htrace : WordTrace (prefixWord ++ tailWord_483128) baseStart_483128 baseEnd_483128 := by
    simpa [prefixWord, tailWord_483128, baseEnd_483128] using wordTrace_append hprefix tailTrace_483128
  have hstable : (prefixWord ++ tailWord_483128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483128).length < 2 ^ (prefixWord ++ tailWord_483128).sum := by decide
  have hdescent : baseEnd_483128 < baseStart_483128 := by decide
  rcases family_descends (prefixWord ++ tailWord_483128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483159 : List Nat := [1, 1, 3, 2, 5, 2, 1, 1, 5]
def baseStart_483159 : Nat := 118140960795 + 483159 * 2 ^ 59
def prefixEnd_483159 : Nat := 4983230072969 + 3 ^ 40 * 483159 * 2
def baseEnd_483159 : Nat := 110263466464791276395777

theorem tailTrace_483159 : CollatzResearch.WordTrace tailWord_483159 prefixEnd_483159 110263466464791276395777 := by
  unfold tailWord_483159
  simp only [CollatzResearch.WordTrace]
  refine ⟨17622256456604934832796531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11748170971069956555197687 17622256456604934832796531)
  ·
    refine ⟨26433384684907402249194797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17622256456604934832796531 26433384684907402249194797)
    ·
      refine ⟨9912519256840275843448049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26433384684907402249194797 9912519256840275843448049)
      ·
        refine ⟨7434389442630206882586037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9912519256840275843448049 7434389442630206882586037)
        ·
          refine ⟨696974010246581895242441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7434389442630206882586037 696974010246581895242441)
          ·
            refine ⟨522730507684936421431831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 696974010246581895242441 522730507684936421431831)
            ·
              refine ⟨784095761527404632147747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522730507684936421431831 784095761527404632147747)
              ·
                refine ⟨1176143642291106948221621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 784095761527404632147747 1176143642291106948221621)
                ·
                  refine ⟨110263466464791276395777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1176143642291106948221621 110263466464791276395777)
                  ·
                    rfl

theorem cell21_483159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 5].length) (baseStart_483159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_483159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_483159 prefixEnd_483159 := by exact prefixLift 483159
  have htrace : WordTrace (prefixWord ++ tailWord_483159) baseStart_483159 baseEnd_483159 := by
    simpa [prefixWord, tailWord_483159, baseEnd_483159] using wordTrace_append hprefix tailTrace_483159
  have hstable : (prefixWord ++ tailWord_483159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483159).length < 2 ^ (prefixWord ++ tailWord_483159).sum := by decide
  have hdescent : baseEnd_483159 < baseStart_483159 := by decide
  rcases family_descends (prefixWord ++ tailWord_483159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483210 : List Nat := [3, 1, 2, 4, 3, 1, 2, 2, 3]
def baseStart_483210 : Nat := 118140960795 + 483210 * 2 ^ 59
def prefixEnd_483210 : Nat := 4983230072969 + 3 ^ 40 * 483210 * 2
def baseEnd_483210 : Nat := 110275105359626521045673

theorem tailTrace_483210 : CollatzResearch.WordTrace tailWord_483210 prefixEnd_483210 110275105359626521045673 := by
  unfold tailWord_483210
  simp only [CollatzResearch.WordTrace]
  refine ⟨4406029144855042635725771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11749411052946780361935389 4406029144855042635725771)
  ·
    refine ⟨6609043717282563953588657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4406029144855042635725771 6609043717282563953588657)
    ·
      refine ⟨4956782787961922965191493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6609043717282563953588657 4956782787961922965191493)
      ·
        refine ⟨929396772742860555973405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4956782787961922965191493 929396772742860555973405)
        ·
          refine ⟨348523789778572708490027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 929396772742860555973405 348523789778572708490027)
          ·
            refine ⟨522785684667859062735041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348523789778572708490027 522785684667859062735041)
            ·
              refine ⟨392089263500894297051281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 522785684667859062735041 392089263500894297051281)
              ·
                refine ⟨294066947625670722788461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 392089263500894297051281 294066947625670722788461)
                ·
                  refine ⟨110275105359626521045673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294066947625670722788461 110275105359626521045673)
                  ·
                    rfl

theorem cell21_483210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 2, 3].length) (baseStart_483210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_483210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_483210 prefixEnd_483210 := by exact prefixLift 483210
  have htrace : WordTrace (prefixWord ++ tailWord_483210) baseStart_483210 baseEnd_483210 := by
    simpa [prefixWord, tailWord_483210, baseEnd_483210] using wordTrace_append hprefix tailTrace_483210
  have hstable : (prefixWord ++ tailWord_483210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483210).length < 2 ^ (prefixWord ++ tailWord_483210).sum := by decide
  have hdescent : baseEnd_483210 < baseStart_483210 := by decide
  rcases family_descends (prefixWord ++ tailWord_483210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483215 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 12]
def baseStart_483215 : Nat := 118140960795 + 483215 * 2 ^ 59
def prefixEnd_483215 : Nat := 4983230072969 + 3 ^ 40 * 483215 * 2
def baseEnd_483215 : Nat := 110276246427747623462329

theorem tailTrace_483215 : CollatzResearch.WordTrace tailWord_483215 prefixEnd_483215 110276246427747623462329 := by
  unfold tailWord_483215
  simp only [CollatzResearch.WordTrace]
  refine ⟨17624298944402056396835099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11749532629601370931223399 17624298944402056396835099)
  ·
    refine ⟨26436448416603084595252649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17624298944402056396835099 26436448416603084595252649)
    ·
      refine ⟨19827336312452313446439487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26436448416603084595252649 19827336312452313446439487)
      ·
        refine ⟨29741004468678470169659231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19827336312452313446439487 29741004468678470169659231)
        ·
          refine ⟨44611506703017705254488847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29741004468678470169659231 44611506703017705254488847)
          ·
            refine ⟨66917260054526557881733271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44611506703017705254488847 66917260054526557881733271)
            ·
              refine ⟨100375890081789836822599907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66917260054526557881733271 100375890081789836822599907)
              ·
                refine ⟨150563835122684755233899861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100375890081789836822599907 150563835122684755233899861)
                ·
                  refine ⟨110276246427747623462329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 150563835122684755233899861 110276246427747623462329)
                  ·
                    rfl

theorem cell21_483215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 12].length) (baseStart_483215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_483215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_483215 prefixEnd_483215 := by exact prefixLift 483215
  have htrace : WordTrace (prefixWord ++ tailWord_483215) baseStart_483215 baseEnd_483215 := by
    simpa [prefixWord, tailWord_483215, baseEnd_483215] using wordTrace_append hprefix tailTrace_483215
  have hstable : (prefixWord ++ tailWord_483215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483215).length < 2 ^ (prefixWord ++ tailWord_483215).sum := by decide
  have hdescent : baseEnd_483215 < baseStart_483215 := by decide
  rcases family_descends (prefixWord ++ tailWord_483215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483334 : List Nat := [6, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_483334 : Nat := 118140960795 + 483334 * 2 ^ 59
def prefixEnd_483334 : Nat := 4983230072969 + 3 ^ 40 * 483334 * 2
def baseEnd_483334 : Nat := 110303403849029860978753

theorem tailTrace_483334 : CollatzResearch.WordTrace tailWord_483334 prefixEnd_483334 110303403849029860978753 := by
  unfold tailWord_483334
  simp only [CollatzResearch.WordTrace]
  refine ⟨550894975967841866263033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11752426153980626480278037 550894975967841866263033)
  ·
    refine ⟨413171231975881399697275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 550894975967841866263033 413171231975881399697275)
    ·
      refine ⟨619756847963822099545913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413171231975881399697275 619756847963822099545913)
      ·
        refine ⟨464817635972866574659435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 619756847963822099545913 464817635972866574659435)
        ·
          refine ⟨697226453959299861989153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464817635972866574659435 697226453959299861989153)
          ·
            refine ⟨522919840469474896491865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 697226453959299861989153 522919840469474896491865)
            ·
              refine ⟨392189880352106172368899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 522919840469474896491865 392189880352106172368899)
              ·
                refine ⟨588284820528159258553349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392189880352106172368899 588284820528159258553349)
                ·
                  refine ⟨110303403849029860978753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 588284820528159258553349 110303403849029860978753)
                  ·
                    rfl

theorem cell21_483334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_483334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_483334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_483334 prefixEnd_483334 := by exact prefixLift 483334
  have htrace : WordTrace (prefixWord ++ tailWord_483334) baseStart_483334 baseEnd_483334 := by
    simpa [prefixWord, tailWord_483334, baseEnd_483334] using wordTrace_append hprefix tailTrace_483334
  have hstable : (prefixWord ++ tailWord_483334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483334).length < 2 ^ (prefixWord ++ tailWord_483334).sum := by decide
  have hdescent : baseEnd_483334 < baseStart_483334 := by decide
  rcases family_descends (prefixWord ++ tailWord_483334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483446 : List Nat := [5, 1, 1, 2, 1, 2, 1, 3, 5]
def baseStart_483446 : Nat := 118140960795 + 483446 * 2 ^ 59
def prefixEnd_483446 : Nat := 4983230072969 + 3 ^ 40 * 483446 * 2
def baseEnd_483446 : Nat := 110328963774942555111857

theorem tailTrace_483446 : CollatzResearch.WordTrace tailWord_483446 prefixEnd_483446 110328963774942555111857 := by
  unfold tailWord_483446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1102045262910323928030887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11755149471043455232329461 1102045262910323928030887)
  ·
    refine ⟨1653067894365485892046331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1102045262910323928030887 1653067894365485892046331)
    ·
      refine ⟨2479601841548228838069497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1653067894365485892046331 2479601841548228838069497)
      ·
        refine ⟨1859701381161171628552123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2479601841548228838069497 1859701381161171628552123)
        ·
          refine ⟨2789552071741757442828185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1859701381161171628552123 2789552071741757442828185)
          ·
            refine ⟨2092164053806318082121139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2789552071741757442828185 2092164053806318082121139)
            ·
              refine ⟨3138246080709477123181709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2092164053806318082121139 3138246080709477123181709)
              ·
                refine ⟨1176842280266053921193141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3138246080709477123181709 1176842280266053921193141)
                ·
                  refine ⟨110328963774942555111857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1176842280266053921193141 110328963774942555111857)
                  ·
                    rfl

theorem cell21_483446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_483446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_483446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_483446 prefixEnd_483446 := by exact prefixLift 483446
  have htrace : WordTrace (prefixWord ++ tailWord_483446) baseStart_483446 baseEnd_483446 := by
    simpa [prefixWord, tailWord_483446, baseEnd_483446] using wordTrace_append hprefix tailTrace_483446
  have hstable : (prefixWord ++ tailWord_483446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483446).length < 2 ^ (prefixWord ++ tailWord_483446).sum := by decide
  have hdescent : baseEnd_483446 < baseStart_483446 := by decide
  rcases family_descends (prefixWord ++ tailWord_483446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483480 : List Nat := [2, 1, 2, 4, 3, 2, 1, 3, 3]
def baseStart_483480 : Nat := 118140960795 + 483480 * 2 ^ 59
def prefixEnd_483480 : Nat := 4983230072969 + 3 ^ 40 * 483480 * 2
def baseEnd_483480 : Nat := 110336723038166051545121

theorem tailTrace_483480 : CollatzResearch.WordTrace tailWord_483480 prefixEnd_483480 110336723038166051545121 := by
  unfold tailWord_483480
  simp only [CollatzResearch.WordTrace]
  refine ⟨8816982144221003327615947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11755976192294671103487929 8816982144221003327615947)
  ·
    refine ⟨13225473216331504991423921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8816982144221003327615947 13225473216331504991423921)
    ·
      refine ⟨9919104912248628743567941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13225473216331504991423921 9919104912248628743567941)
      ·
        refine ⟨1859832171046617889418989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9919104912248628743567941 1859832171046617889418989)
        ·
          refine ⟨697437064142481708532121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1859832171046617889418989 697437064142481708532121)
          ·
            refine ⟨523077798106861281399091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 697437064142481708532121 523077798106861281399091)
            ·
              refine ⟨784616697160291922098637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523077798106861281399091 784616697160291922098637)
              ·
                refine ⟨294231261435109470786989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 784616697160291922098637 294231261435109470786989)
                ·
                  refine ⟨110336723038166051545121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294231261435109470786989 110336723038166051545121)
                  ·
                    rfl

theorem cell21_483480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 3, 3].length) (baseStart_483480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_483480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_483480 prefixEnd_483480 := by exact prefixLift 483480
  have htrace : WordTrace (prefixWord ++ tailWord_483480) baseStart_483480 baseEnd_483480 := by
    simpa [prefixWord, tailWord_483480, baseEnd_483480] using wordTrace_append hprefix tailTrace_483480
  have hstable : (prefixWord ++ tailWord_483480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483480).length < 2 ^ (prefixWord ++ tailWord_483480).sum := by decide
  have hdescent : baseEnd_483480 < baseStart_483480 := by decide
  rcases family_descends (prefixWord ++ tailWord_483480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483567 : List Nat := [1, 1, 2, 1, 6, 3, 1, 6]
def baseStart_483567 : Nat := 118140960795 + 483567 * 2 ^ 59
def prefixEnd_483567 : Nat := 4983230072969 + 3 ^ 40 * 483567 * 2
def baseEnd_483567 : Nat := 36785525874491077864981

theorem tailTrace_483567 : CollatzResearch.WordTrace tailWord_483567 prefixEnd_483567 36785525874491077864981 := by
  unfold tailWord_483567
  simp only [CollatzResearch.WordTrace]
  refine ⟨17637137439126820513648955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11758091626084547009099303 17637137439126820513648955)
  ·
    refine ⟨26455706158690230770473433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17637137439126820513648955 26455706158690230770473433)
    ·
      refine ⟨19841779619017673077855075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26455706158690230770473433 19841779619017673077855075)
      ·
        refine ⟨29762669428526509616782613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19841779619017673077855075 29762669428526509616782613)
        ·
          refine ⟨1395125129462180138286685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29762669428526509616782613 1395125129462180138286685)
          ·
            refine ⟨523171923548317551857507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1395125129462180138286685 523171923548317551857507)
            ·
              refine ⟨784757885322476327786261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523171923548317551857507 784757885322476327786261)
              ·
                refine ⟨36785525874491077864981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 784757885322476327786261 36785525874491077864981)
                ·
                  rfl

theorem cell21_483567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 6].length) (baseStart_483567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_483567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_483567 prefixEnd_483567 := by exact prefixLift 483567
  have htrace : WordTrace (prefixWord ++ tailWord_483567) baseStart_483567 baseEnd_483567 := by
    simpa [prefixWord, tailWord_483567, baseEnd_483567] using wordTrace_append hprefix tailTrace_483567
  have hstable : (prefixWord ++ tailWord_483567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483567).length < 2 ^ (prefixWord ++ tailWord_483567).sum := by decide
  have hdescent : baseEnd_483567 < baseStart_483567 := by decide
  rcases family_descends (prefixWord ++ tailWord_483567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483595 : List Nat := [1, 1, 1, 1, 5, 2, 2, 2, 6]
def baseStart_483595 : Nat := 118140960795 + 483595 * 2 ^ 59
def prefixEnd_483595 : Nat := 4983230072969 + 3 ^ 40 * 483595 * 2
def baseEnd_483595 : Nat := 110362967604951407128219

theorem tailTrace_483595 : CollatzResearch.WordTrace tailWord_483595 prefixEnd_483595 110362967604951407128219 := by
  unfold tailWord_483595
  simp only [CollatzResearch.WordTrace]
  refine ⟨17638158683025381295668239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11758772455350254197112159 17638158683025381295668239)
  ·
    refine ⟨26457238024538071943502359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17638158683025381295668239 26457238024538071943502359)
    ·
      refine ⟨39685857036807107915253539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26457238024538071943502359 39685857036807107915253539)
      ·
        refine ⟨59528785555210661872880309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39685857036807107915253539 59528785555210661872880309)
        ·
          refine ⟨5580823645800999550582529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59528785555210661872880309 5580823645800999550582529)
          ·
            refine ⟨4185617734350749662936897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5580823645800999550582529 4185617734350749662936897)
            ·
              refine ⟨3139213300763062247202673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4185617734350749662936897 3139213300763062247202673)
              ·
                refine ⟨2354409975572296685402005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3139213300763062247202673 2354409975572296685402005)
                ·
                  refine ⟨110362967604951407128219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2354409975572296685402005 110362967604951407128219)
                  ·
                    rfl

theorem cell21_483595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 6].length) (baseStart_483595 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_483595 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_483595 prefixEnd_483595 := by exact prefixLift 483595
  have htrace : WordTrace (prefixWord ++ tailWord_483595) baseStart_483595 baseEnd_483595 := by
    simpa [prefixWord, tailWord_483595, baseEnd_483595] using wordTrace_append hprefix tailTrace_483595
  have hstable : (prefixWord ++ tailWord_483595).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483595).length < 2 ^ (prefixWord ++ tailWord_483595).sum := by decide
  have hdescent : baseEnd_483595 < baseStart_483595 := by decide
  rcases family_descends (prefixWord ++ tailWord_483595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
